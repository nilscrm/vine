//! Compiles specializations of VIR into bytecode for the frames runtime.
//!
//! Each specialization is compiled into one [`Unit`]; its stages become code
//! within the unit, connected by jumps, and its locals live in registers.
//! Blocks enter a unit at its entry points (e.g. a function's start), and at
//! the points where it resumes after waiting for a value.
//!
//! See [`unit`] for how a single unit is compiled.

mod unit;

use std::collections::{HashMap, HashSet};

use frames::program::{Block, BlockId, Instr, IoOp, Label, Program, Reg, Unit, UnitId};
use vine_util::idx::IdxVec;

use crate::{
  components::layouter::{Layout, Layouter, Term},
  structures::{
    ast::Span,
    chart::{Chart, GenericsId},
    diag::{Diag, Diags, ErrorGuaranteed},
    intrinsics::Intrinsic,
    resolutions::{Fragment, FragmentId, Resolutions},
    signatures::Signatures,
    specializations::{ImplTreeId, SpecId, SpecKind, Specializations},
    types::{ImplType, Type, TypeKind, Types},
    vir::{StageId, Vir},
  },
};

pub struct FramesEmitter<'a> {
  pub(crate) chart: &'a Chart,
  pub(crate) sigs: &'a Signatures,
  pub(crate) fragments: &'a IdxVec<FragmentId, Fragment>,
  pub(crate) vir: &'a IdxVec<FragmentId, Vir>,
  pub(crate) specs: &'a Specializations,
  pub(crate) layouter: Layouter<'a>,
  pub program: Program,
  /// The intrinsic implemented by each fragment, if any.
  intrinsics: HashMap<FragmentId, Intrinsic>,
  /// The implementation arguments of each specialization of a fragment.
  spec_args: HashMap<SpecId, Vec<ImplTreeId>>,
  /// Blocks entering specializations at given stages.
  entries: HashMap<(SpecId, StageId), BlockId>,
  queue: Vec<SpecId>,
  queued: HashSet<SpecId>,
  /// Blocks whose frames discard a value of a given size.
  discard: HashMap<u32, BlockId>,
}

impl<'a> FramesEmitter<'a> {
  pub fn new(
    chart: &'a Chart,
    sigs: &'a Signatures,
    resolutions: &'a Resolutions,
    fragments: &'a IdxVec<FragmentId, Fragment>,
    vir: &'a IdxVec<FragmentId, Vir>,
    specs: &'a Specializations,
    diags: &'a mut Diags,
  ) -> Self {
    let mut intrinsics = HashMap::new();
    for (fn_id, fn_def) in chart.concrete_fns.iter() {
      if let Some(intrinsic) = fn_def.intrinsic
        && let Some(&fragment) = resolutions.fns.get(fn_id)
      {
        intrinsics.insert(fragment, intrinsic);
      }
    }
    let mut spec_args = HashMap::new();
    for lookup in specs.lookup.values() {
      for (args, &spec_id) in lookup {
        spec_args.insert(spec_id, args.clone());
      }
    }
    FramesEmitter {
      chart,
      sigs,
      fragments,
      vir,
      specs,
      layouter: Layouter::new(chart, sigs, specs, diags),
      program: Program::default(),
      intrinsics,
      spec_args,
      entries: HashMap::new(),
      queue: Vec::new(),
      queued: HashSet::new(),
      discard: HashMap::new(),
    }
  }

  /// Compiles the program whose entrypoint is the specialization `main`, of a
  /// function `fn main(&io: &IO)`.
  pub fn emit(mut self, main: SpecId) -> Result<Program, ErrorGuaranteed> {
    let main_block = self.entry(main, StageId(0));

    // The entry unit calls `main` with an IO handle, and a space for the final
    // IO handle, which halts the program once written.
    let halt = self.program.blocks.push(Block { unit: UnitId(0), entry: Label(0), frame: vec![] });
    let r = Reg;
    let entry_unit = self.program.units.push(Unit {
      name: "entry".into(),
      regs: 6,
      code: vec![
        // entry
        Instr::NewFrame { dst: r(0), block: halt },
        Instr::Space { dst: r(2), frame: r(0), offset: 1 },
        Instr::Const { dst: r(1), value: 0 },
        Instr::NewFrame { dst: r(3), block: main_block },
        Instr::Fill { frame: r(3), offset: 1, src: r(1), len: 2 },
        Instr::End,
        // halt
        Instr::Io { op: IoOp::Flush, args: vec![r(5)], rets: vec![r(5)] },
        Instr::Halt,
        Instr::End,
      ],
    });
    self.program.blocks[halt] = Block { unit: entry_unit, entry: Label(6), frame: vec![r(5)] };
    self.program.entry =
      self.program.blocks.push(Block { unit: entry_unit, entry: Label(0), frame: vec![] });

    while let Some(spec_id) = self.queue.pop() {
      self.emit_spec(spec_id);
    }

    self.layouter.diags.bail()?;
    Ok(self.program)
  }

  /// Returns the block entering `spec_id` at `stage`, queuing the
  /// specialization to be compiled if necessary.
  pub(crate) fn entry(&mut self, spec_id: SpecId, stage: StageId) -> BlockId {
    *self.entries.entry((spec_id, stage)).or_insert_with(|| {
      if self.queued.insert(spec_id) {
        self.queue.push(spec_id);
      }
      self.program.blocks.push(Block { unit: UnitId(usize::MAX), entry: Label(0), frame: vec![] })
    })
  }

  fn emit_spec(&mut self, spec_id: SpecId) {
    let spec = self.specs.spec(spec_id);
    match &spec.kind {
      SpecKind::Fragment(fragment_id) => {
        let (unit_id, entries) = unit::emit_unit(self, spec_id, *fragment_id);
        for (stage, entry, frame) in entries {
          if let Some(&block) = self.entries.get(&(spec_id, stage)) {
            self.program.blocks[block] = Block { unit: unit_id, entry, frame };
          }
        }
      }
      SpecKind::Synthetic(item) => {
        self.error(Diag::FramesUnsupported { span: Span::NONE, what: format!("{item:?}") });
      }
    }
  }

  /// Returns a block whose frames receive a value of `len` words, and discard
  /// it.
  pub(crate) fn discard_block(&mut self, len: u32) -> BlockId {
    if let Some(&block) = self.discard.get(&len) {
      return block;
    }
    let unit =
      self.program.units.push(Unit { name: "discard".into(), regs: len, code: vec![Instr::End] });
    let block =
      self.program.blocks.push(Block { unit, entry: Label(0), frame: (0..len).map(Reg).collect() });
    self.discard.insert(len, block);
    block
  }

  pub(crate) fn intrinsic(&self, spec_id: SpecId) -> Option<Intrinsic> {
    match self.specs.spec(spec_id).kind {
      SpecKind::Fragment(fragment) => self.intrinsics.get(&fragment).copied(),
      SpecKind::Synthetic(_) => None,
    }
  }

  /// The layouts of the type parameters of a specialization of a fragment.
  pub(crate) fn type_param_terms(
    &mut self,
    spec_id: SpecId,
    generics: GenericsId,
  ) -> Result<Vec<Term>, ErrorGuaranteed> {
    let args = self.spec_args.get(&spec_id).cloned().unwrap_or_default();
    let impl_params = &self.sigs.impl_params[generics].types;
    let count = self.sigs.type_params[generics].params.len();
    let mut terms = vec![None; count];
    for (index, ty) in impl_params.inner.iter().enumerate() {
      if let ImplType::Trait(trait_id, tys) = ty
        && Some(*trait_id) == self.chart.builtins.layout
        && let Some((_, TypeKind::Param(param, _))) = impl_params.types.kind(tys[0])
      {
        terms[*param] = Some(self.layouter.impl_tree_term(args[index])?);
      }
    }
    Ok(terms.into_iter().map(|t| t.expect("missing layout parameter")).collect())
  }

  pub(crate) fn layout(
    &mut self,
    types: &Types,
    ty: Type,
    params: &[Term],
  ) -> Result<Layout, ErrorGuaranteed> {
    self.layouter.type_layout(types, ty, params)
  }

  pub(crate) fn error(&mut self, diag: Diag) -> ErrorGuaranteed {
    self.layouter.diags.error(diag)
  }
}
