//! Compiles one specialization of a fragment into a [`Unit`].
//!
//! # Wires
//!
//! Every VIR wire connects a *writer*, which produces the wire's value, and a
//! *reader*, which consumes it; a port whose type is inverted is the writer.
//! Whichever end is emitted first records itself, and the second completes the
//! connection. A writer either produces the value in registers, or, if it can
//! only deliver the value later (e.g. a call's result), it asks for a *space*
//! to write it into: if the reader forwards the value into a space itself, the
//! writer gets that space; otherwise, the value is *held* by a hole.
//!
//! # Waiting
//!
//! Code is emitted in program order, but only waits where the data requires
//! it. A value which is not available yet is held by a hole: writing it into a
//! space forwards the hole, and moving it only changes which registers it
//! belongs in. A step which reads such values (e.g. an operation, or building a
//! string) is emitted into a *task* of its own: a frame of this unit which
//! receives the values the step reads, and spaces for the values it writes, and
//! runs the step once they have all arrived (see `emit_detached`). The code
//! emitting it goes on without waiting, so the step waits only for its own
//! inputs, as in a dataflow graph.
//!
//! Only control flow waits: a branch or match on a value which is not available
//! yet, and locals passed to another stage, *suspend*. The values waited for
//! arrive in a *continuation frame*, along with the live registers; the block
//! ends, and execution resumes at a new entry point once the frame is ready.
//! Locals whose values are produced by code after the transfer (e.g. which are
//! borrowed by a reference the target takes, or whose final value is read) are
//! passed in holes instead (`lazy_inputs`).
//!
//! # Control flow
//!
//! Stages are code within the unit. A transfer which is the last step of a
//! stage is a jump; an earlier transfer is like a call, which returns to the
//! step after it once a stage without a final transfer is reached. Locals are
//! kept in fixed registers, so they need no work at stage boundaries; the
//! interfaces' wires say which locals are valid where.

use std::{
  collections::{BTreeMap, HashMap},
  env,
  mem::{swap, take},
};

use frames::program::{Block, BlockId, Instr, IoOp, Label, Reg, Unit, UnitId};
use vine_util::idx::IdxVec;

use crate::{
  components::{
    frames::FramesEmitter,
    layouter::{Layout, Term},
    synthesizer::SyntheticItem,
  },
  structures::{
    ast::Span,
    diag::Diag,
    intrinsics::Intrinsic,
    resolutions::{ConstRelId, FnRelId, Fragment, FragmentId},
    specializations::{SpecId, SpecKind},
    tir::Local,
    types::{Type, TypeKind},
    vir::{
      Header, InterfaceId, InterfaceKind, Invocation, Port, PortKind, StageId, Step, Transfer, Vir,
      WireId,
    },
  },
};

type WireKey = (StageId, WireId);

#[derive(Debug, Clone, Copy)]
enum WireState {
  /// The value is in these registers, some of which may be pending.
  Value(Reg, u32),
  /// The reader has been emitted: a local, which takes the value once it has
  /// been produced.
  ReaderLocal(Local),
  /// The reader has been emitted: the value must be written into this space.
  ReaderSpace(Reg),
  /// The value of a local at the end of the stage; read by a header.
  LocalAtEnd(Local),
  /// The reader has been emitted, and discards the value.
  Discard,
  Consumed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LocalState {
  Empty,
  /// The local's value is in its registers (some of which may be pending).
  Valid,
  /// The local's value is the value of this wire, which has not been produced
  /// yet.
  Alias(WireKey),
  /// The local's value is the value another local has when the current scope
  /// ends.
  AtEnd(Local),
}

/// The state inherited from the stage which transferred into a layer.
#[derive(Debug, Clone)]
struct Context {
  /// Registers holding values of enclosing stages, which must be preserved.
  outer: Vec<(Reg, u32)>,
  locals: IdxVec<Local, LocalState>,
  /// Spaces to write locals' final values into when the scope ends.
  at_end: Vec<(Local, AtEnd)>,
  /// The space the entry point's result is written into.
  ret_space: Option<Reg>,
  /// The entry point's result.
  result: Option<(WireKey, Port)>,
  /// The locals the current chain of stages returns, once control returns to
  /// the step after the transfer which started it: the outputs of that
  /// transfer's interface.
  owed: Vec<Local>,
}

impl Context {
  fn new(locals: usize) -> Self {
    Context {
      outer: Vec::new(),
      locals: IdxVec::from_iter((0..locals).map(|_| LocalState::Empty)),
      at_end: Vec::new(),
      ret_space: None,
      result: None,
      owed: Vec::new(),
    }
  }
}

/// A frame of this unit which receives values that are not available yet,
/// and runs code once they have all arrived, while the code which created it
/// goes on; e.g. a step which reads a call's result.
struct Task {
  frame: Reg,
  block: BlockId,
  /// The register each of the frame's words is loaded into.
  map: Vec<Reg>,
  code: Vec<Instr>,
}

impl Task {
  /// The offset of the frame's next word.
  fn offset(&self) -> u32 {
    1 + self.map.len() as u32
  }
}

/// The state of the code being emitted, and of the values it works with; a
/// task's code is emitted with a state of its own.
#[derive(Default)]
struct Flow {
  code: Vec<Instr>,
  wires: HashMap<WireKey, WireState>,
  pending: HashMap<Reg, usize>,
  cont: Option<Cont>,
  virtual_spaces: HashMap<Reg, Vec<Reg>>,
  unwritten: HashMap<Reg, (Reg, usize)>,
  held: HashMap<Reg, (Reg, usize)>,
  holes: HashMap<Reg, Vec<Reg>>,
  in_task: HashMap<Reg, (usize, Reg)>,
  temps: Vec<(Reg, u32)>,
}

struct Cont {
  frame: Reg,
  block: BlockId,
  /// The register each of the frame's words is loaded into.
  map: Vec<Reg>,
}

/// A port, as seen by the step it belongs to.
struct PortInfo {
  key: Option<WireKey>,
  writer: bool,
  /// The type of the value carried by the wire.
  ty: Type,
  layout: Layout,
}

enum Fixup {
  Stage(StageId),
  Return(ReturnPoint),
}

/// Where control goes once a stage finishes without a final transfer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ReturnPoint {
  /// The fragment returns.
  Fragment,
  /// The step after a transfer.
  After(StageId, usize),
}

/// Compiles a specialization of a fragment, pushing its unit, and returns its
/// entry points: the stage, the label, and the registers its frame is loaded
/// into.
pub(super) fn emit_unit(
  e: &mut FramesEmitter<'_>,
  spec_id: SpecId,
  fragment_id: FragmentId,
) -> (UnitId, Vec<(StageId, Label, Vec<Reg>)>) {
  let fragment = &e.fragments[fragment_id];
  let vir = &e.vir[fragment_id];
  let unit = e.program.units.push(Unit { name: fragment.path.clone(), regs: 0, code: vec![] });
  let Ok(params) = e.type_param_terms(spec_id, fragment.generics) else { return (unit, vec![]) };
  let mut builder = UnitBuilder {
    e,
    spec_id,
    fragment,
    vir,
    params,
    unit,
    code: Vec::new(),
    next_reg: 0,
    stage: StageId(0),
    step: 0,
    stage_ended: false,
    wires: HashMap::new(),
    locals: IdxVec::from_iter(vir.locals.keys().map(|_| LocalState::Empty)),
    local_regs: HashMap::new(),
    outer: Vec::new(),
    pending: HashMap::new(),
    cont: None,
    virtual_spaces: HashMap::new(),
    unwritten: HashMap::new(),
    held: HashMap::new(),
    holes: HashMap::new(),
    lazy_returns: HashMap::new(),
    lazy_inputs: HashMap::new(),
    lazy_locals: Vec::new(),
    temps: Vec::new(),
    tasks: Vec::new(),
    open_tasks: Vec::new(),
    in_task: HashMap::new(),
    reader_tasks: HashMap::new(),
    extra_wires: usize::MAX,
    ret_space: None,
    result: None,
    owed: Vec::new(),
    at_end: Vec::new(),
    stage_labels: HashMap::new(),
    fixups: Vec::new(),
    returns: HashMap::new(),
    return_labels: HashMap::new(),
    interface_data: HashMap::new(),
    queue: Vec::new(),
    entries: Vec::new(),
  };
  builder.emit();
  let UnitBuilder { code, next_reg, entries, .. } = builder;
  if env::var("FRAMES_DEBUG").is_ok() {
    let stages = entries.iter().map(|e| e.0).collect::<Vec<_>>();
    eprintln!("{}: entries {stages:?}", fragment.path);
  }
  e.program.units[unit] = Unit { name: fragment.path.clone(), regs: next_reg, code };
  (unit, entries)
}

struct UnitBuilder<'e, 'a> {
  e: &'e mut FramesEmitter<'a>,
  spec_id: SpecId,
  fragment: &'a Fragment,
  vir: &'a Vir,
  params: Vec<Term>,
  unit: UnitId,
  code: Vec<Instr>,
  next_reg: u32,

  stage: StageId,
  step: usize,
  stage_ended: bool,
  wires: HashMap<WireKey, WireState>,
  locals: IdxVec<Local, LocalState>,
  local_regs: HashMap<Local, (Reg, u32)>,
  outer: Vec<(Reg, u32)>,

  /// Pending registers, and the index of the continuation frame's word they
  /// will be loaded from.
  pending: HashMap<Reg, usize>,
  cont: Option<Cont>,
  /// Registers holding *virtual* spaces, and the registers their words are
  /// written into. A virtual space only exists at compile time, for a value
  /// that will be produced by this unit's own code; it only becomes a real
  /// space, pointing into the continuation frame, when it escapes the unit.
  virtual_spaces: HashMap<Reg, Vec<Reg>>,
  /// Registers that will be written through a virtual space; the space, and
  /// the index of the word.
  unwritten: HashMap<Reg, (Reg, usize)>,
  /// Registers whose values are held by a hole; the register holding the
  /// hole, and the index of the word.
  held: HashMap<Reg, (Reg, usize)>,
  /// Registers holding holes, and the registers their words belong in.
  holes: HashMap<Reg, Vec<Reg>>,
  /// For each point a child stage returns to, the locals it returns which are
  /// only passed on there, and the registers of the holes returning them; the
  /// code after the return point is shared by every path returning to it.
  lazy_returns: HashMap<ReturnPoint, Vec<(Local, Reg)>>,
  /// For each interface, the locals passed to it in holes, and the registers
  /// of the holes; all transfers into an interface agree on these.
  lazy_inputs: HashMap<InterfaceId, Vec<(Local, Reg)>>,
  /// The locals which were passed to the current stage in holes.
  lazy_locals: Vec<Local>,
  /// Registers read by the current step, which must be preserved if it
  /// suspends.
  temps: Vec<(Reg, u32)>,
  /// Finished tasks, whose code is placed after the unit's other code.
  tasks: Vec<Task>,
  /// Tasks which further steps may be emitted into, until the current block
  /// ends.
  open_tasks: Vec<Task>,
  /// Registers whose values are computed by an open task: the task, and the
  /// task's register holding the value.
  in_task: HashMap<Reg, (usize, Reg)>,
  /// Open tasks created for steps which will read values written into them,
  /// by the index of the step.
  reader_tasks: HashMap<usize, usize>,
  /// The id of the next wire created by the emitter, counting down.
  extra_wires: usize,

  ret_space: Option<Reg>,
  /// The header's result, written when the fragment returns.
  result: Option<(WireKey, Port)>,
  owed: Vec<Local>,
  /// Spaces to write locals' final values into when the current scope ends.
  at_end: Vec<(Local, AtEnd)>,

  stage_labels: HashMap<StageId, Label>,
  fixups: Vec<(usize, usize, Fixup)>,
  /// Where each stage returns to.
  returns: HashMap<StageId, ReturnPoint>,
  return_labels: HashMap<ReturnPoint, Label>,
  /// The registers holding the data passed through an interface (e.g. the
  /// value matched on).
  interface_data: HashMap<InterfaceId, (Reg, u32)>,
  /// Stages to emit, with the state they are entered with.
  queue: Vec<(StageId, Context)>,
  entries: Vec<(StageId, Label, Vec<Reg>)>,
}

impl UnitBuilder<'_, '_> {
  fn emit(&mut self) {
    if !self.compute_returns() {
      return;
    }
    // The fragment is entered at its first stage, and at the stages of its
    // closures.
    for stage in self.roots() {
      self.queue.push((stage, Context::new(self.vir.locals.len())));
    }
    while let Some((stage, context)) = self.queue.pop() {
      if !self.stage_labels.contains_key(&stage) {
        self.emit_stage(stage, &context);
      }
    }
    for (index, target, fixup) in take(&mut self.fixups) {
      let label = match fixup {
        Fixup::Stage(stage) => self.stage_labels[&stage],
        Fixup::Return(point) => self.return_labels[&point],
      };
      set_target(&mut self.code[index], target, label);
    }
    for task in take(&mut self.tasks) {
      let base = self.code.len() as u32;
      self.code.extend(task.code.into_iter().map(|mut instr| {
        relocate(&mut instr, base);
        instr
      }));
      self.e.program.blocks[task.block] =
        Block { unit: self.unit, entry: Label(base), frame: task.map };
    }
  }

  /// The stages the unit is entered at.
  fn roots(&self) -> Vec<StageId> {
    let mut roots = vec![StageId(0)];
    for (_, interface) in self.vir.interfaces.iter() {
      if let InterfaceKind::Closure { .. } = interface.kind {
        roots.extend(interface.kind.stages());
      }
    }
    roots
  }

  /// Determines where each stage returns to, which must be unique.
  fn compute_returns(&mut self) -> bool {
    let mut queue =
      self.roots().into_iter().map(|stage| (stage, ReturnPoint::Fragment)).collect::<Vec<_>>();
    while let Some((stage_id, point)) = queue.pop() {
      if let Some(&existing) = self.returns.get(&stage_id) {
        if existing != point {
          self.unsupported_error("a stage with several return points".into());
          return false;
        }
        continue;
      }
      self.returns.insert(stage_id, point);
      let steps = &self.vir.stages[stage_id].steps;
      for (index, step) in steps.iter().enumerate() {
        if let Step::Transfer(transfer) = step
          && !creates_value(&self.vir.interfaces[transfer.interface].kind)
        {
          let target_point =
            if index + 1 == steps.len() { point } else { ReturnPoint::After(stage_id, index) };
          for target in self.vir.interfaces[transfer.interface].kind.stages() {
            queue.push((target, target_point));
          }
        }
      }
    }
    true
  }

  fn emit_stage(&mut self, stage_id: StageId, context: &Context) {
    let stage = &self.vir.stages[stage_id];
    self.stage = stage_id;
    self.stage_ended = false;
    self.stage_labels.insert(stage_id, self.label());
    self.outer = context.outer.clone();
    self.locals = context.locals.clone();
    self.at_end = context.at_end.clone();
    self.ret_space = context.ret_space;
    self.result = context.result.clone();
    self.owed = context.owed.clone();
    debug_assert!(self.cont.is_none() && self.pending.is_empty());
    self.virtual_spaces.clear();
    self.unwritten.clear();
    self.held.clear();
    self.holes.clear();
    self.temps.clear();
    debug_assert!(self.open_tasks.is_empty());
    self.in_task.clear();
    self.reader_tasks.clear();

    let interface = &self.vir.interfaces[stage.interface];
    for (&local, &(input, _, _)) in &interface.wires {
      self.locals[local] = if input { LocalState::Valid } else { LocalState::Empty };
    }
    self.lazy_locals.clear();
    for (local, hole) in self.lazy_inputs.get(&stage.interface).cloned().unwrap_or_default() {
      let (reg, len) = self.local_regs(local);
      self.hold_regs(hole, (0..len).map(|i| reg.offset(i)).collect());
      self.locals[local] = LocalState::Valid;
      self.lazy_locals.push(local);
    }

    self.emit_header(stage_id);

    // Steps which only move data are emitted once their inputs are available;
    // e.g. destructuring patterns are emitted before the steps producing the
    // value they destructure.
    let mut deferred = Vec::new();
    for (index, step) in stage.steps.iter().enumerate() {
      if self.stage_ended {
        break;
      }
      self.step = index;
      if moves_data(step) {
        deferred.push((index, step));
        self.emit_deferred(&mut deferred, false);
        continue;
      }
      self.emit_deferred(&mut deferred, true);
      if self.waits(step) {
        self.emit_detached(index, step);
      } else {
        self.emit_step(index, step);
      }
      self.emit_deferred(&mut deferred, false);
    }
    self.emit_deferred(&mut deferred, true);
    if let Some(&(index, step)) = deferred.first() {
      self.step = index;
      if env::var("FRAMES_DEBUG").is_ok() {
        eprintln!("stuck: {step:?}");
        for (key, state) in &self.wires {
          if key.0 == self.stage {
            eprintln!("  {key:?}: {state:?}");
          }
        }
      }
      self.unsupported("a value used before it is computed".into());
    }

    if !self.stage_ended {
      self.end_stage();
    }
  }

  fn emit_header(&mut self, stage_id: StageId) {
    let stage = &self.vir.stages[stage_id];
    let label = self.label();
    match &stage.header {
      Header::Bare => {}
      Header::Fn(params, result) => {
        let mut map = Vec::new();
        self.header_params(params, &mut map);
        self.header_result(result, &mut map);
        self.entries.push((stage_id, label, map));
      }
      // A closure is called, forked, or dropped with the closure as the first
      // argument.
      Header::Closure(params, result) => {
        let closure = self.alloc(1);
        let mut map = vec![closure];
        self.header_params(params, &mut map);
        self.header_result(result, &mut map);
        self.entries.push((stage_id, label, map));
        self.open_closure(stage.interface, closure);
      }
      Header::Fork(former, latter) => {
        // `fork(&self) -> Self`; the stage creates two closures, the latter of
        // which is written back into the reference.
        let regs = self.alloc(3);
        let map = vec![regs, regs.offset(1), regs.offset(2)];
        self.entries.push((stage_id, label, map));
        self.wire_reader_space(latter, regs.offset(1));
        self.wire_reader_space(former, regs.offset(2));
        self.open_closure(stage.interface, regs);
      }
      Header::Drop => {
        let closure = self.alloc(1);
        self.entries.push((stage_id, label, vec![closure]));
        self.open_closure(stage.interface, closure);
      }
      Header::Const(result) => {
        let mut map = Vec::new();
        self.header_result(result, &mut map);
        self.entries.push((stage_id, label, map));
      }
      Header::Match(_, _, data) => {
        let (reg, _) = self.interface_data[&stage.interface];
        let info = self.port_info(data);
        if info.layout.size != 0 {
          self.set_wire(info.key.unwrap(), WireState::Value(reg.offset(1), info.layout.size));
        }
      }
      header => {
        self.unsupported(format!("{header:?}"));
      }
    }
  }

  fn header_params(&mut self, params: &[Port], map: &mut Vec<Reg>) {
    for param in params {
      let info = self.port_info(param);
      if info.layout.size == 0 {
        continue;
      }
      if info.writer {
        let reg = self.alloc(info.layout.size);
        map.extend((0..info.layout.size).map(|i| reg.offset(i)));
        self.set_wire(info.key.unwrap(), WireState::Value(reg, info.layout.size));
      } else {
        let space = self.alloc(1);
        map.push(space);
        self.wire_reader_space(param, space);
      }
    }
  }

  fn header_result(&mut self, result: &Port, map: &mut Vec<Reg>) {
    let info = self.port_info(result);
    if info.layout.size != 0 {
      let space = self.alloc(1);
      map.push(space);
      self.ret_space = Some(space);
    }
    match info.key {
      Some(key) => self.result = Some((key, result.clone())),
      None if info.layout.size != 0 => {
        // A constant; it is returned immediately.
        let value = self.read_value(result);
        let space = self.ret_space.take().unwrap();
        self.write_back(space, value);
      }
      None => {}
    }
  }

  fn end_stage(&mut self) {
    match self.returns[&self.stage] {
      ReturnPoint::Fragment => {
        if let Some((key, _)) = self.result.clone()
          && let Some(ret_space) = self.ret_space
        {
          match self.wires.get(&key).copied() {
            Some(WireState::LocalAtEnd(local)) => {
              let (reg, len) = self.local_value(local);
              self.locals[local] = LocalState::Empty;
              self.write_back(ret_space, (reg, len));
            }
            Some(WireState::Value(reg, len)) => self.write_back(ret_space, (reg, len)),
            None => {
              self.wires.insert(key, WireState::ReaderSpace(ret_space));
            }
            state => unreachable!("{state:?}"),
          }
        }
        self.emit_at_end();
        for local in self.locals.keys().collect::<Vec<_>>() {
          self.drop_local(local);
        }
        self.suspend();
        self.code.push(Instr::End);
      }
      point @ ReturnPoint::After(..) => {
        self.emit_at_end();
        let lazy = self.lazy_returns.get(&point).cloned().unwrap_or_default();
        let mut moves = Vec::new();
        for local in self.locals.keys().collect::<Vec<_>>() {
          if !self.owed.contains(&local) {
            self.drop_local(local);
            continue;
          }
          if self.locals[local] == LocalState::Empty {
            continue;
          }
          let (reg, len) = self.local_value(local);
          match lazy.iter().find(|&&(l, _)| l == local) {
            Some(&(_, canonical)) if len != 0 => {
              let hole = self.hole_holding(reg, len);
              self.temps.push((hole, 1));
              moves.push((canonical, hole));
            }
            _ => self.resolve(reg, len),
          }
        }
        self.suspend();
        for (canonical, hole) in moves {
          self.code.push(Instr::Move { dst: canonical, src: hole, len: 1 });
        }
        self.fixups.push((self.code.len(), 0, Fixup::Return(point)));
        self.code.push(Instr::Jump { target: Label(0) });
      }
    }
    self.stage_ended = true;
  }

  /// Emits deferred steps whose inputs are available. Steps which are not
  /// settled are only emitted if `unsettled` is true, as they would wait
  /// for values unnecessarily.
  fn emit_deferred(&mut self, deferred: &mut Vec<(usize, &Step)>, unsettled: bool) {
    loop {
      let mut found = deferred.iter().position(|(_, step)| self.ready(step) && self.settled(step));
      if found.is_none() && unsettled {
        found = deferred.iter().position(|(_, step)| self.ready(step));
      }
      let Some(i) = found else { break };
      let (index, step) = deferred.remove(i);
      self.step = index;
      self.emit_step(index, step);
    }
  }

  /// Whether the readers of the fields a step produces spaces for are known;
  /// otherwise, the spaces would point into the continuation frame, and later
  /// code would wait for their values.
  fn settled(&mut self, step: &Step) -> bool {
    let fields: Vec<&Port> = match step {
      Step::Composite(port, fields) if self.port_info(port).writer => fields.iter().collect(),
      Step::Ref(reference, value, space) if self.port_info(reference).writer => {
        vec![value, space]
      }
      _ => return true,
    };
    fields.into_iter().all(|port| {
      let info = self.port_info(port);
      match info.key {
        Some(key) => !info.writer || info.layout.size == 0 || self.wires.contains_key(&key),
        None => true,
      }
    })
  }

  /// Whether a step which only moves data has its inputs available; other
  /// steps are always emitted in order.
  fn ready(&mut self, step: &Step) -> bool {
    let inputs: Vec<&Port> = match step {
      Step::Composite(port, fields) => {
        if self.port_info(port).writer {
          fields.iter().filter(|f| !self.port_info(f).writer).collect()
        } else {
          vec![port]
        }
      }
      Step::Ref(reference, value, space) => {
        if self.port_info(reference).writer {
          [value, space].into_iter().filter(|p| !self.port_info(p).writer).collect()
        } else {
          vec![reference]
        }
      }
      Step::Rewrap(a, b) | Step::Link(a, b) | Step::Union(_, _, a, b) => {
        if self.writes_first(a, b) { vec![b] } else { vec![a] }
      }
      Step::Enum(_, _, _, data) => vec![data],
      _ => return true,
    };
    inputs.into_iter().all(|port| {
      let info = self.port_info(port);
      match info.key {
        Some(key) => info.layout.size == 0 || self.wires.contains_key(&key),
        None => true,
      }
    })
  }

  /// Writes locals' final values into the spaces waiting for them.
  fn emit_at_end(&mut self) {
    while !self.at_end.is_empty() {
      self.emit_at_end_entry(0);
    }
  }

  /// Writes the final values of locals for which `keep` is false, as their
  /// scope ends.
  fn emit_at_end_except(&mut self, keep: impl Fn(&Self, Local) -> bool) {
    let mut i = 0;
    while i < self.at_end.len() {
      let mut local = self.at_end[i].0;
      while let LocalState::AtEnd(other) = self.locals[local] {
        local = other;
      }
      if self.locals[local] == LocalState::Empty || keep(self, local) {
        i += 1;
      } else {
        self.emit_at_end_entry(i);
      }
    }
  }

  /// Writes a local's final value as the `at_end` entry at `index` says, and
  /// removes the entry. It stays in `at_end` until then, so that its register
  /// is preserved if this waits.
  fn emit_at_end_entry(&mut self, index: usize) {
    let (local, action) = self.at_end[index];
    if let Some(local) = self.final_local(local) {
      match (action, self.locals[local]) {
        (AtEnd::Forward(hole, len), _) => {
          // The local's final value is a space, which the hole's value is
          // forwarded into.
          let (space, _) = self.local_value(local);
          self.locals[local] = LocalState::Empty;
          if self.remote(space, 1) {
            // The space is not available yet; a task forwards the value into
            // it once it is.
            let mut task = self.new_task();
            let space = self.task_input(&mut task, space, 1);
            let hole = self.task_input(&mut task, hole, 1);
            task.code.push(Instr::HoleForward { hole, space, len });
            self.finish_task(task);
          } else {
            self.materialize(space);
            self.code.push(Instr::HoleForward { hole, space, len });
          }
        }
        (AtEnd::Write(space), _) => {
          let (reg, len) = self.local_value(local);
          self.locals[local] = LocalState::Empty;
          self.write_back(space, (reg, len));
        }
      }
    }
    self.at_end.remove(index);
  }

  /// Records that `local`'s value is `other`'s final value; spaces waiting
  /// for `local`'s final value now wait for `other`'s.
  fn set_at_end(&mut self, local: Local, other: Local) {
    self.locals[local] = LocalState::AtEnd(other);
    for (waiting, _) in &mut self.at_end {
      if *waiting == local {
        *waiting = other;
      }
    }
  }

  /// Follows locals whose values are other locals' final values.
  fn final_local(&mut self, mut local: Local) -> Option<Local> {
    for _ in 0..self.vir.locals.len() {
      match self.locals[local] {
        LocalState::AtEnd(other) => local = other,
        LocalState::Empty => {
          if env::var("FRAMES_DEBUG").is_ok() {
            eprintln!("final_local: {local:?} empty; locals {:?}", self.locals);
          }
          self.unsupported("a local read before it is written".into());
          return None;
        }
        _ => return Some(local),
      }
    }
    None
  }

  fn emit_step(&mut self, index: usize, step: &Step) {
    self.temps.clear();
    match step {
      Step::Invoke(span, local, invocation) => {
        self.emit_invocation(index, *span, *local, invocation)
      }
      Step::Transfer(transfer) => self.emit_transfer(index, transfer),
      Step::Diverge(..) => unreachable!(),
      Step::Link(a, b) | Step::Rewrap(a, b) => self.emit_link(a, b),
      Step::Call(span, rel, args, ret) => self.emit_call(*span, *rel, args, ret),
      Step::Const(span, rel, port) => self.emit_const(*span, *rel, port),
      Step::Composite(port, fields) => self.emit_composite(port, fields),
      Step::Ref(reference, value, space) => self.emit_ref(reference, value, space),
      Step::Enum(_, variant, port, data) => {
        let info = self.port_info(port);
        let data = self.read_value(data);
        let reg = self.alloc(info.layout.size);
        self.code.push(Instr::Const { dst: reg, value: variant.0 as u64 });
        self.move_regs(reg.offset(1), data.0, data.1);
        for i in 1 + data.1..info.layout.size {
          self.code.push(Instr::Const { dst: reg.offset(i), value: 0 });
        }
        self.write_value(port, reg, info.layout.size);
      }
      Step::Union(_, _, a, b) => {
        let (union, data) = if self.port_info(a).layout.size >= self.port_info(b).layout.size {
          (a, b)
        } else {
          (b, a)
        };
        let union_info = self.port_info(union);
        if union_info.writer {
          let data = self.read_value(data);
          let reg = self.alloc(union_info.layout.size);
          self.move_regs(reg, data.0, data.1);
          for i in data.1..union_info.layout.size {
            self.code.push(Instr::Const { dst: reg.offset(i), value: 0 });
          }
          self.write_value(union, reg, union_info.layout.size);
        } else {
          let (reg, _) = self.read_value(union);
          let size = self.port_info(data).layout.size;
          self.write_value(data, reg, size);
        }
      }
      Step::BoolNot(a, b) => self.emit_op("bool:not", &[a], Some(b)),
      Step::BoolAnd(a, b, c) => self.emit_op("bool:and", &[a, b], Some(c)),
      Step::List(port, elements) => {
        let info = self.port_info(port);
        let element_size = self.list_element_size(info.ty);
        let parts =
          elements.iter().map(|element| ListPart::Value(self.read_value(element))).collect();
        let list = self.build_list(element_size, parts);
        self.write_value(port, list, 3);
      }
      Step::String(port, init, rest) => {
        let mut parts = init.chars().map(ListPart::Char).collect::<Vec<_>>();
        for (string, literal) in rest {
          parts.push(ListPart::List(self.read_value(string).0));
          parts.extend(literal.chars().map(ListPart::Char));
        }
        let list = self.build_list(1, parts);
        self.write_value(port, list, 3);
      }
      Step::InlineIvy(..) => self.unsupported("inline Ivy".into()),
    }
  }

  // Locals

  fn local_regs(&mut self, local: Local) -> (Reg, u32) {
    if let Some(&regs) = self.local_regs.get(&local) {
      return regs;
    }
    let ty = self.vir.locals[local].ty;
    let size = self.layout(ty).size;
    let reg = self.alloc(size);
    self.local_regs.insert(local, (reg, size));
    (reg, size)
  }

  /// Ensures that the local's value is in its registers (which may be
  /// pending).
  fn local_value(&mut self, local: Local) -> (Reg, u32) {
    let regs = self.local_regs(local);
    if let LocalState::AtEnd(_) = self.locals[local] {
      self.unsupported("a value used before it is computed".into());
      self.locals[local] = LocalState::Valid;
    }
    if let LocalState::Alias(key) = self.locals[local] {
      match self.wires.get(&key).copied() {
        Some(WireState::Value(reg, len)) => {
          self.move_regs(regs.0, reg, len);
          self.wires.insert(key, WireState::Consumed);
          self.locals[local] = LocalState::Valid;
        }
        Some(WireState::LocalAtEnd(other)) => {
          self.wires.insert(key, WireState::Consumed);
          self.set_at_end(local, other);
          return self.local_value(local);
        }
        _ => {
          self.unsupported("a value used before it is computed".into());
          self.locals[local] = LocalState::Valid;
        }
      }
    }
    regs
  }

  fn emit_invocation(&mut self, index: usize, span: Span, local: Local, invocation: &Invocation) {
    if self.vir.locals[local].inv.0 {
      self.unsupported("inverted locals".into());
      return;
    }
    match invocation {
      Invocation::Barrier => self.drop_local(local),
      Invocation::Read(port) => self.read_local(index, span, local, port, true),
      Invocation::ReadBarrier(port) => {
        self.read_local(index, span, local, port, false);
        self.drop_local(local);
      }
      Invocation::ReadWrite(read, write) => {
        self.read_local(index, span, local, read, false);
        self.write_local(local, write);
      }
      Invocation::Write(port) | Invocation::BarrierWrite(port) => {
        self.drop_local(local);
        self.write_local(local, port);
      }
    }
  }

  fn read_local(&mut self, index: usize, span: Span, local: Local, port: &Port, may_fork: bool) {
    let info = self.port_info(port);
    if info.layout.size == 0 {
      if let Some(key) = info.key {
        self.wires.insert(key, WireState::Consumed);
      }
      return;
    }
    if self.locals[local] == LocalState::Empty {
      // The local is read before it is written; this reads the value it has
      // when the current scope ends.
      if !info.writer {
        // The local holds a space, which the wire's value is written into;
        // the value is held in a hole until then.
        let hole = self.alloc(1);
        self.code.push(Instr::HoleNew { dst: hole, len: info.layout.size });
        let space = self.alloc(1);
        self.code.push(Instr::Space { dst: space, frame: hole, offset: 1 });
        self.wire_reader_space(port, space);
        self.at_end.push((local, AtEnd::Forward(hole, info.layout.size)));
      } else if let Some(key) = info.key {
        self.set_wire(key, WireState::LocalAtEnd(local));
      }
      return;
    }
    let (reg, len) = self.local_value(local);
    if !info.writer {
      // The local holds a space; the wire's value is written into it.
      self.locals[local] = LocalState::Empty;
      let space = self.alloc(len);
      self.move_regs(space, reg, len);
      self.wire_reader_space(port, space);
      return;
    }
    if may_fork && self.used_later(index, local) {
      let copy = self.fork(span, local);
      self.write_value(port, copy, len);
    } else {
      self.locals[local] = LocalState::Empty;
      let new = self.alloc(len);
      self.move_regs(new, reg, len);
      self.write_value(port, new, len);
    }
  }

  fn write_local(&mut self, local: Local, port: &Port) {
    let info = self.port_info(port);
    if info.layout.size == 0 {
      if let Some(key) = info.key {
        self.wires.insert(key, WireState::Consumed);
      }
      self.locals[local] = LocalState::Valid;
      return;
    }
    if info.writer {
      // The local holds a space, which the wire's value is written into.
      let space = self.wire_space(port);
      let (reg, _) = self.local_regs(local);
      self.move_regs(reg, space, 1);
      self.locals[local] = LocalState::Valid;
      return;
    }
    let Some(key) = info.key else {
      // A constant.
      let (reg, len) = self.read_value(port);
      let regs = self.local_regs(local);
      self.move_regs(regs.0, reg, len);
      self.locals[local] = LocalState::Valid;
      return;
    };
    match self.wires.get(&key).copied() {
      Some(WireState::Value(reg, len)) => {
        let regs = self.local_regs(local);
        self.move_regs(regs.0, reg, len);
        // The local may be larger, e.g. if its type is an `if const`, whose
        // layout fits either branch.
        for i in len..regs.1 {
          self.code.push(Instr::Const { dst: regs.0.offset(i), value: 0 });
        }
        self.wires.insert(key, WireState::Consumed);
        self.locals[local] = LocalState::Valid;
      }
      Some(WireState::LocalAtEnd(other)) => {
        self.wires.insert(key, WireState::Consumed);
        self.set_at_end(local, other);
      }
      None => {
        self.wires.insert(key, WireState::ReaderLocal(local));
        self.locals[local] = LocalState::Alias(key);
      }
      Some(state) => unreachable!("{state:?}"),
    }
  }

  /// Drops the local's value, if it has one.
  fn drop_local(&mut self, local: Local) {
    match self.locals[local] {
      LocalState::Empty => {}
      // The value is owned by the other local.
      LocalState::AtEnd(_) => self.locals[local] = LocalState::Empty,
      LocalState::Alias(_) | LocalState::Valid => {
        let (reg, len) = self.local_value(local);
        self.locals[local] = LocalState::Empty;
        if len == 0 {
          return;
        }
        match self.vir.locals[local].drop {
          Some(rel) => self.call_rel(Span::NONE, rel, vec![CallArg::Regs(reg, len)], None),
          // Holes holding the value are still read, to free them.
          None => self.discard_held(reg, len),
        }
      }
    }
  }

  /// Forks the local's value, returning registers holding the copy.
  fn fork(&mut self, span: Span, local: Local) -> Reg {
    let (reg, len) = self.local_value(local);
    let copy = self.alloc(len);
    let Some(rel) = self.vir.locals[local].fork else {
      self.unsupported("forking a local without a `Fork` implementation".into());
      return copy;
    };
    // `fork(&self) -> T`; the reference is the value, and a space for the value
    // afterwards.
    self.call_rel(span, rel, vec![CallArg::Ref(reg, len)], Some((copy, len)));
    copy
  }

  /// Whether the local has its final value: it has a value, and is not
  /// changed by the rest of the stage.
  fn is_final(&self, local: Local) -> bool {
    if !matches!(self.locals[local], LocalState::Valid | LocalState::Alias(_)) {
      return false;
    }
    let stage = &self.vir.stages[self.stage];
    stage.steps.iter().skip(self.step + 1).all(|step| match step {
      Step::Invoke(_, l, _) => *l != local,
      Step::Transfer(transfer) => {
        !self.vir.interfaces[transfer.interface].wires.contains_key(&local)
      }
      _ => true,
    })
  }

  /// Whether the local's current value is used after the step at `index`.
  fn used_later(&self, index: usize, local: Local) -> bool {
    let stage = &self.vir.stages[self.stage];
    for (index, step) in stage.steps.iter().enumerate().skip(index + 1) {
      match step {
        Step::Invoke(_, l, invocation) if *l == local => {
          return matches!(
            invocation,
            Invocation::Read(_) | Invocation::ReadBarrier(_) | Invocation::ReadWrite(..)
          );
        }
        Step::Transfer(transfer) => {
          let interface = &self.vir.interfaces[transfer.interface];
          if let Some(&(input, _, output)) = interface.wires.get(&local) {
            if input {
              return true;
            }
            if output {
              return false;
            }
          }
          if index + 1 == stage.steps.len() && !creates_value(&interface.kind) {
            // A final transfer; the stage ends here.
            return false;
          }
        }
        _ => {}
      }
    }
    // Its final value is read.
    if self.owed.contains(&local)
      || self.at_end.iter().any(|&(l, _)| l == local)
      || self.wires.iter().any(|(key, state)| {
        key.0 == self.stage && matches!(state, WireState::LocalAtEnd(l) if *l == local)
      })
    {
      return true;
    }
    let interface = &self.vir.interfaces[stage.interface];
    matches!(interface.wires.get(&local), Some(&(_, _, true)))
  }

  // Control flow

  fn emit_transfer(&mut self, index: usize, transfer: &Transfer) {
    let interface = &self.vir.interfaces[transfer.interface];
    match interface.kind {
      InterfaceKind::Closure { .. } => return self.emit_closure(index, transfer),
      InterfaceKind::Inspect(_) => return self.unsupported("inspect".into()),
      _ => {}
    }
    let stage = &self.vir.stages[self.stage];
    let child = index + 1 != stage.steps.len();

    let data = transfer.data.as_ref().map(|data| self.read_value(data));

    // Locals the target only reads, which this stage keeps: the target gets a
    // copy.
    let mut kept = Vec::new();
    if child {
      for (&local, &(input, barrier, output)) in &interface.wires {
        if input
          && !barrier
          && !output
          && self.locals[local] != LocalState::Empty
          && self.used_later(index, local)
        {
          let (_, len) = self.local_regs(local);
          let copy = self.fork(Span::NONE, local);
          kept.push((local, copy, len));
        }
      }
    }

    // If the stage ends here, the locals the target takes are passed on, and
    // those the chain of stages returns are kept, until control returns. The
    // scopes of other locals end.
    let owed = self.owed.clone();
    let keep = |local: Local| {
      matches!(interface.wires.get(&local), Some(&(true, _, _))) || owed.contains(&local)
    };
    if !child {
      self.emit_at_end_except(|_, local| keep(local));
    }

    // Locals whose values are produced by code after this transfer (e.g. a
    // local whose final value is read before it is written, or which is
    // borrowed by a reference the target takes), or which were passed to this
    // stage in holes, are passed in holes, so that only the code which reads
    // them waits for them. Other locals are waited for here. All transfers into
    // an interface agree on which locals are passed in holes.
    let lazy = match self.lazy_inputs.get(&transfer.interface) {
      Some(lazy) => lazy.clone(),
      None => {
        let mut lazy = Vec::new();
        for local in self.locals.keys().collect::<Vec<_>>() {
          let input = matches!(interface.wires.get(&local), Some(&(true, _, _)));
          if !input && (child || !owed.contains(&local)) {
            continue;
          }
          let (reg, len) = self.local_regs(local);
          let waits = (input && self.locals[local] == LocalState::Empty)
            || (self.locals[local] != LocalState::Empty
              && ((0..len).any(|i| self.unwritten.contains_key(&reg.offset(i)))
                || (self.lazy_locals.contains(&local) && self.local_waits(local))));
          if len != 0 && waits {
            lazy.push((local, self.alloc(1)));
          }
        }
        self.lazy_inputs.insert(transfer.interface, lazy.clone());
        lazy
      }
    };
    if !child {
      // Spaces for final values of locals which the target writes.
      for &(_, action) in &self.at_end.clone() {
        self.materialize(action.reg());
      }
    }
    for &(local, canonical) in &lazy {
      let hole = if self.locals[local] == LocalState::Empty {
        // Its value once the current scope ends.
        let (_, len) = self.local_regs(local);
        let hole = self.alloc(1);
        self.code.push(Instr::HoleNew { dst: hole, len });
        let space = self.alloc(1);
        self.code.push(Instr::Space { dst: space, frame: hole, offset: 1 });
        self.at_end.push((local, AtEnd::Write(space)));
        hole
      } else {
        let (reg, len) = self.local_value(local);
        self.locals[local] = LocalState::Empty;
        self.hole_holding(reg, len)
      };
      self.code.push(Instr::Move { dst: canonical, src: hole, len: 1 });
      self.temps.push((canonical, 1));
    }

    // Pass the locals the target needs; they are kept in their registers.
    // Holds and virtual spaces only exist while the current stage is emitted,
    // so they are resolved and made real.
    for (&local, &(input, _, _)) in &interface.wires {
      if input && self.locals[local] != LocalState::Empty {
        let (reg, len) = self.local_value(local);
        self.materialize_range(reg, len);
        self.resolve(reg, len);
      }
    }
    if !child {
      for local in self.locals.keys().collect::<Vec<_>>() {
        if !keep(local) {
          self.drop_local(local);
        } else if self.locals[local] != LocalState::Empty {
          let (reg, len) = self.local_value(local);
          self.materialize_range(reg, len);
          self.resolve(reg, len);
        }
      }
    }
    // The copies are preserved if this waits.
    self.temps.extend(kept.iter().map(|&(_, copy, len)| (copy, len)));
    if let Some((reg, len)) = data {
      self.materialize_range(reg, len);
      self.require(reg, len);
    }
    self.suspend();

    let target_context = if child {
      let mut outer = self.outer.clone();
      outer.extend(self.live_wires());
      outer.extend(self.ret_space.map(|r| (r, 1)));
      outer.extend(self.at_end.iter().map(|&(_, action)| (action.reg(), 1)));
      // The child only sees the locals of its interface; the others stay with
      // this stage.
      let locals = IdxVec::from_iter(self.locals.keys().map(|_| LocalState::Empty));
      let valid = self.locals.iter().filter(|&(local, &state)| {
        state == LocalState::Valid && !matches!(interface.wires.get(&local), Some(&(true, _, _)))
      });
      for local in valid.map(|(l, _)| l).collect::<Vec<_>>() {
        outer.push(self.local_regs(local));
      }
      outer.extend(kept.iter().map(|&(_, copy, len)| (copy, len)));
      // Held registers are preserved by preserving their holes.
      let outer = self.live_regs(outer);
      Context {
        outer,
        locals,
        at_end: Vec::new(),
        ret_space: self.ret_space,
        result: self.result.clone(),
        owed: interface.wires.iter().filter(|(_, w)| w.2).map(|(&local, _)| local).collect(),
      }
    } else {
      Context {
        outer: self.outer.clone(),
        locals: self.locals.clone(),
        at_end: self.at_end.clone(),
        ret_space: self.ret_space,
        result: self.result.clone(),
        owed,
      }
    };
    // A branch on a constant only emits the stage taken; the other may not be
    // supported (e.g. the debug mode of `IfConst`).
    let constant = match interface.kind {
      InterfaceKind::Branch(then, else_) => {
        self.constant_condition(transfer).map(|b| if b { then } else { else_ })
      }
      _ => None,
    };
    for target in interface.kind.stages() {
      if constant.is_none_or(|stage| stage == target) {
        self.queue.push((target, target_context.clone()));
      }
    }

    match &interface.kind {
      InterfaceKind::Unconditional(target) => self.jump(*target),
      InterfaceKind::Branch(..) if constant.is_some() => self.jump(constant.unwrap()),
      InterfaceKind::Branch(then, else_) => {
        let (cond, _) = data.unwrap();
        self.fixups.push((self.code.len(), 0, Fixup::Stage(*then)));
        self.fixups.push((self.code.len(), 1, Fixup::Stage(*else_)));
        self.code.push(Instr::Branch { cond, then: Label(0), else_: Label(0) });
      }
      InterfaceKind::Match(_, stages) => {
        let (reg, len) = data.unwrap();
        let canonical = *self.interface_data.entry(transfer.interface).or_insert_with(|| {
          let reg = Reg(self.next_reg);
          self.next_reg += len;
          (reg, len)
        });
        self.move_regs(canonical.0, reg, len);
        for (i, &stage) in stages.iter().enumerate() {
          self.fixups.push((self.code.len(), i, Fixup::Stage(stage)));
        }
        self.code.push(Instr::Switch { tag: canonical.0, targets: vec![Label(0); stages.len()] });
      }
      kind => self.unsupported(format!("{kind:?}")),
    }

    if child {
      let point = ReturnPoint::After(self.stage, index);
      self.return_labels.insert(point, self.label());
      for (&local, &(input, _, output)) in &interface.wires {
        if output {
          self.locals[local] = LocalState::Valid;
        } else if input {
          self.locals[local] = LocalState::Empty;
        }
      }
      // Returned locals which are only passed on are returned in holes.
      let mut lazy = Vec::new();
      for (&local, &(_, _, output)) in &interface.wires {
        if output && self.local_passed_on(index, local) {
          let (reg, len) = self.local_regs(local);
          if len != 0 {
            let hole = self.alloc(1);
            self.hold_regs(hole, (0..len).map(|i| reg.offset(i)).collect());
            lazy.push((local, hole));
          }
        }
      }
      self.lazy_returns.insert(point, lazy);
      for (local, copy, len) in kept {
        let (reg, _) = self.local_regs(local);
        self.move_regs(reg, copy, len);
        self.locals[local] = LocalState::Valid;
      }
    } else {
      self.stage_ended = true;
    }
  }

  /// The value of a branch's condition, if it is a constant boolean.
  fn constant_condition(&self, transfer: &Transfer) -> Option<bool> {
    let PortKind::Wire(_, wire) = transfer.data.as_ref()?.kind else { return None };
    let stage = &self.vir.stages[self.stage];
    stage.steps.iter().find_map(|step| match step {
      Step::Const(_, rel, port) if matches!(port.kind, PortKind::Wire(_, w) if w == wire) => {
        self.constant_bool(self.e.specs.spec(self.spec_id).rels.consts[*rel].ok()?, 0)
      }
      _ => None,
    })
  }

  fn constant_bool(&self, spec: SpecId, depth: usize) -> Option<bool> {
    if depth > 8 {
      return None;
    }
    let spec = self.e.specs.spec(spec);
    match &spec.kind {
      // The frames runtime has no debug mode.
      SpecKind::Fragment(fragment)
        if Some(self.e.fragments[*fragment].def) == self.e.chart.builtins.debug_enabled =>
      {
        Some(false)
      }
      SpecKind::Fragment(fragment) => {
        let vir = &self.e.vir[*fragment];
        let stage = vir.stages.values().next()?;
        match &stage.header {
          Header::Const(Port { kind: PortKind::Bool(b), .. }) => Some(*b),
          _ => None,
        }
      }
      SpecKind::Synthetic(SyntheticItem::ConstAlias(_)) => {
        self.constant_bool(spec.rels.consts[ConstRelId(0)].ok()?, depth + 1)
      }
      SpecKind::Synthetic(_) => None,
    }
  }

  fn jump(&mut self, stage: StageId) {
    self.fixups.push((self.code.len(), 0, Fixup::Stage(stage)));
    self.code.push(Instr::Jump { target: Label(0) });
  }

  // Closures

  /// The words of the environment of a closure: for each local the closure's
  /// stages take as input, its value; for each local they output, a space for
  /// its final value.
  fn closure_env(&mut self, interface: InterfaceId) -> Vec<(Local, EnvWords)> {
    let mut env = Vec::new();
    for (&local, &(input, _, output)) in &self.vir.interfaces[interface].wires {
      let (_, len) = self.local_regs(local);
      if len == 0 {
        continue;
      }
      if input {
        env.push((local, EnvWords::Value(len)));
      }
      if output {
        env.push((local, EnvWords::Space));
      }
    }
    env
  }

  /// Creates a closure: a hole holding its environment.
  fn emit_closure(&mut self, index: usize, transfer: &Transfer) {
    let interface = &self.vir.interfaces[transfer.interface];
    let env = self.closure_env(transfer.interface);
    let size = env.iter().map(|(_, words)| words.len()).sum::<u32>();
    let closure = self.alloc(1);
    if size == 0 {
      self.code.push(Instr::Const { dst: closure, value: 0 });
    } else {
      let regs = self.alloc(size);
      let mut offset = 0;
      for &(local, words) in &env {
        let dst = regs.offset(offset);
        match words {
          EnvWords::Value(len) => {
            if self.locals[local] == LocalState::Empty {
              self.unsupported("a local read before it is written".into());
            } else {
              let (_, barrier, output) = interface.wires[&local];
              if !barrier && !output && self.used_later(index, local) {
                let copy = self.fork(Span::NONE, local);
                self.move_regs(dst, copy, len);
              } else {
                let (reg, _) = self.local_value(local);
                self.locals[local] = LocalState::Empty;
                self.move_regs(dst, reg, len);
              }
            }
          }
          EnvWords::Space => {
            // The local's final value is written back by the closure, into a
            // hole.
            let (reg, len) = self.local_regs(local);
            let space = self.pending_space(reg, len);
            self.hold(space);
            self.move_regs(dst, space, 1);
            self.locals[local] = LocalState::Valid;
          }
        }
        offset += words.len();
      }
      // Values which are not available yet are forwarded into the hole once
      // they are.
      self.code.push(Instr::HoleNew { dst: closure, len: size });
      let space = self.alloc(1);
      self.code.push(Instr::Space { dst: space, frame: closure, offset: 1 });
      self.temps.push((closure, 1));
      self.emit_write(space, regs, size);
    }
    if let Some(data) = &transfer.data {
      self.write_value(data, closure, 1);
    }
  }

  /// Takes a closure's environment, at the start of one of its stages; its
  /// values become the values of locals, and its spaces receive the final
  /// values of locals.
  fn open_closure(&mut self, interface: InterfaceId, closure: Reg) {
    let env = self.closure_env(interface);
    let size = env.iter().map(|(_, words)| words.len()).sum::<u32>();
    if size == 0 {
      return;
    }
    for &(local, _) in &env {
      self.locals[local] = LocalState::Empty;
    }
    let regs = self.alloc(size);
    let ok = self.alloc(1);
    self.code.push(Instr::HoleTake { hole: closure, dst: regs, len: size, ok });
    let branch = self.code.len();
    self.code.push(Instr::Branch { cond: ok, then: Label(0), else_: Label(branch as u32 + 1) });
    // The environment is not complete yet; wait for it.
    let space = self.pending_space(regs, size);
    self.materialize_cont(space);
    self.code.push(Instr::HoleForward { hole: closure, space, len: size });
    self.suspend();
    let resume = self.label();
    set_target(&mut self.code[branch], 0, resume);

    let mut offset = 0;
    for (local, words) in env {
      let src = regs.offset(offset);
      match words {
        EnvWords::Value(len) => {
          let (reg, _) = self.local_regs(local);
          self.move_regs(reg, src, len);
          self.locals[local] = LocalState::Valid;
        }
        EnvWords::Space => self.at_end.push((local, AtEnd::Write(src))),
      }
      offset += words.len();
    }
  }

  // Calls

  fn emit_call(&mut self, span: Span, rel: FnRelId, args: &[Port], ret: &Port) {
    let Ok((callee, _)) = self.e.specs.spec(self.spec_id).rels.fns[rel] else { return };
    if let Some(intrinsic) = self.e.intrinsic(callee) {
      return self.emit_intrinsic(span, intrinsic, args, ret);
    }
    if let SpecKind::Synthetic(item) = &self.e.specs.spec(callee).kind {
      let item = item.clone();
      return self.emit_synthetic(span, callee, &item, args, ret);
    }
    let args = args.iter().map(|arg| CallArg::Port(arg.clone())).collect();
    let ret_info = self.port_info(ret);
    let ret = (ret_info.layout.size != 0).then(|| CallRet::Port(ret.clone()));
    self.call(span, CallTarget::Rel(rel), args, ret);
  }

  fn call_rel(&mut self, span: Span, rel: FnRelId, args: Vec<CallArg>, ret: Option<(Reg, u32)>) {
    let Ok((callee, _)) = self.e.specs.spec(self.spec_id).rels.fns[rel] else { return };
    match self.e.intrinsic(callee) {
      Some(Intrinsic::Duplicate) => {
        let [CallArg::Ref(reg, len)] = args[..] else { unreachable!() };
        let (copy, _) = ret.unwrap();
        self.duplicate(reg, len, copy);
      }
      Some(Intrinsic::Erase | Intrinsic::Forget) => {
        // Holes holding the value are still read, to free them.
        if let [CallArg::Regs(reg, len)] = args[..] {
          self.discard_held(reg, len);
        }
      }
      _ => self.call(span, CallTarget::Rel(rel), args, ret.map(|(r, l)| CallRet::Regs(r, l))),
    }
  }

  /// Copies plain data into `copy`.
  fn duplicate(&mut self, reg: Reg, len: u32, copy: Reg) {
    if self.remote(reg, len) {
      // The value is not available yet; a task copies it once it is.
      let mut task = self.new_task();
      let value = self.task_input(&mut task, reg, len);
      let original = self.task_output(&mut task, reg, len);
      let copied = self.task_output(&mut task, copy, len);
      task.code.push(Instr::Write { space: original, src: value, len });
      task.code.push(Instr::Write { space: copied, src: value, len });
      self.finish_task(task);
    } else {
      self.code.push(Instr::Move { dst: copy, src: reg, len });
    }
  }

  fn call(&mut self, _span: Span, target: CallTarget, args: Vec<CallArg>, ret: Option<CallRet>) {
    let (callee, stage) = match target {
      CallTarget::Rel(rel) => match self.e.specs.spec(self.spec_id).rels.fns[rel] {
        Ok(x) => x,
        Err(_) => return,
      },
      CallTarget::Spec(spec, stage) => (spec, stage),
    };
    // Gather the arguments' values before allocating the frame, as this may
    // suspend.
    let mut words = Vec::new();
    for arg in &args {
      words.push(match arg {
        CallArg::Port(port) => {
          let info = self.port_info(port);
          if info.layout.size == 0 {
            continue;
          }
          if info.writer {
            ArgWords::Space(self.wire_space(port))
          } else if info.key.is_some_and(|key| !self.wires.contains_key(&key)) {
            // The value has not been produced yet; it will be written directly
            // into the callee's frame.
            ArgWords::Forward(port.clone(), info.layout.size)
          } else {
            let (reg, len) = self.read_value(port);
            self.require_filled(reg, len);
            ArgWords::Regs(reg, len)
          }
        }
        CallArg::Regs(reg, len) => {
          self.require_filled(*reg, *len);
          ArgWords::Regs(*reg, *len)
        }
        CallArg::Ref(reg, len) => {
          self.require_filled(*reg, *len);
          ArgWords::Ref(*reg, *len)
        }
      });
    }
    if words.is_empty() && ret.is_none() && self.trivial(callee) {
      return;
    }
    let block = self.e.entry(callee, stage);
    let frame = self.alloc(1);
    self.code.push(Instr::NewFrame { dst: frame, block });
    let mut offset = 1;
    for words in words {
      match words {
        ArgWords::Regs(reg, len) => {
          self.emit_fill(frame, offset, reg, len);
          offset += len;
        }
        ArgWords::Space(space) => {
          self.emit_fill(frame, offset, space, 1);
          offset += 1;
        }
        ArgWords::Forward(port, len) => {
          let space = self.alloc(1);
          self.code.push(Instr::Space { dst: space, frame, offset });
          self.wire_reader_space(&port, space);
          offset += len;
        }
        ArgWords::Ref(reg, len) => {
          // The value, and a space for the value afterwards, which is written
          // back into the same registers.
          self.emit_fill(frame, offset, reg, len);
          let space = self.pending_space(reg, len);
          self.emit_fill(frame, offset + len, space, 1);
          offset += len + 1;
        }
      }
    }
    if let Some(ret) = ret {
      let space = match ret {
        CallRet::Port(port) => self.wire_space(&port),
        CallRet::Regs(reg, len) => self.pending_space(reg, len),
      };
      self.emit_fill(frame, offset, space, 1);
    }
  }

  fn emit_const(&mut self, span: Span, rel: ConstRelId, port: &Port) {
    let Ok(callee) = self.e.specs.spec(self.spec_id).rels.consts[rel] else { return };
    self.emit_const_spec(span, callee, port);
  }

  fn emit_const_spec(&mut self, span: Span, callee: SpecId, port: &Port) {
    if let SpecKind::Synthetic(item) = &self.e.specs.spec(callee).kind {
      let item = item.clone();
      return self.emit_synthetic(span, callee, &item, &[], port);
    }
    let info = self.port_info(port);
    if info.layout.size == 0 {
      // Evaluating it has no effect.
      return;
    }
    if info.layout.size == 1
      && let Some(value) = self.constant_word(callee, 0)
    {
      let reg = self.alloc(1);
      self.code.push(Instr::Const { dst: reg, value });
      return self.write_value(port, reg, 1);
    }
    self.call(
      span,
      CallTarget::Spec(callee, StageId(0)),
      vec![],
      Some(CallRet::Port(port.clone())),
    );
  }

  /// The value of a constant which is a literal word, if it is one.
  fn constant_word(&self, spec: SpecId, depth: usize) -> Option<u64> {
    if depth > 8 {
      return None;
    }
    if let Some(b) = self.constant_bool(spec, 0) {
      return Some(b as u64);
    }
    let spec = self.e.specs.spec(spec);
    match &spec.kind {
      SpecKind::Fragment(fragment) => {
        let stage = self.e.vir[*fragment].stages.values().next()?;
        match &stage.header {
          Header::Const(Port { kind: PortKind::N32(n), .. }) => Some(*n as u64),
          Header::Const(Port { kind: PortKind::F32(f), .. }) => Some(f.to_bits() as u64),
          Header::Const(Port { kind: PortKind::F64(f), .. }) => Some(f.to_bits()),
          _ => None,
        }
      }
      SpecKind::Synthetic(SyntheticItem::ConstAlias(_)) => {
        self.constant_word(spec.rels.consts[ConstRelId(0)].ok()?, depth + 1)
      }
      SpecKind::Synthetic(SyntheticItem::N32(n)) => Some(*n as u64),
      SpecKind::Synthetic(_) => None,
    }
  }

  /// Whether a function only moves data, so that calling it without inputs or
  /// outputs has no effect (e.g. dropping `()`).
  fn trivial(&self, spec: SpecId) -> bool {
    let SpecKind::Fragment(fragment) = self.e.specs.spec(spec).kind else { return false };
    self.e.vir[fragment].stages.values().all(|stage| {
      stage
        .steps
        .iter()
        .all(|step| !matches!(step, Step::Call(..) | Step::Const(..) | Step::InlineIvy(..)))
    })
  }

  fn emit_synthetic(
    &mut self,
    span: Span,
    spec: SpecId,
    item: &SyntheticItem,
    args: &[Port],
    ret: &Port,
  ) {
    match item {
      SyntheticItem::N32(n) => {
        let reg = self.alloc(1);
        self.code.push(Instr::Const { dst: reg, value: *n as u64 });
        self.write_value(ret, reg, 1);
      }
      SyntheticItem::ConstNil => {}
      SyntheticItem::DebugState => {
        // Debug mode is not supported; the debug state is `None()`.
        let size = self.port_info(ret).layout.size;
        let reg = self.alloc(size);
        for i in 0..size {
          self.code.push(Instr::Const { dst: reg.offset(i), value: 0 });
        }
        self.write_value(ret, reg, size);
      }
      SyntheticItem::Identity | SyntheticItem::CompositeDeconstruct(_) => {
        // These only reinterpret a value's words.
        let (reg, len) = self.read_value(&args[0]);
        self.write_value(ret, reg, len);
      }
      SyntheticItem::CompositeReconstruct(_) => {
        // The composite's words are those of its first field, followed by those
        // of the rest.
        let size = self.port_info(ret).layout.size;
        let out = self.alloc(size);
        let mut offset = 0;
        for arg in args {
          let (reg, len) = self.read_value(arg);
          self.move_regs(out.offset(offset), reg, len);
          offset += len;
        }
        self.write_value(ret, out, size);
      }
      SyntheticItem::String(string) => {
        let list = self.build_list(1, string.chars().map(ListPart::Char).collect());
        self.write_value(ret, list, 3);
      }
      SyntheticItem::EnumVariantNames(enum_id) => {
        let names = self.e.chart.enums[*enum_id].variants.values().map(|v| v.name.0.clone());
        let names = names.collect::<Vec<_>>();
        let parts = names
          .iter()
          .map(|name| {
            ListPart::Value((self.build_list(1, name.chars().map(ListPart::Char).collect()), 3))
          })
          .collect();
        let list = self.build_list(3, parts);
        self.write_value(ret, list, 3);
      }
      SyntheticItem::ConstAlias(_) => {
        let Ok(target) = self.e.specs.spec(spec).rels.consts[ConstRelId(0)] else { return };
        self.emit_const_spec(span, target, ret);
      }
      SyntheticItem::CallFn(..) => {
        // `call(f, (params...)) -> ret`, where `f` is empty; the parameters
        // are passed on as they are.
        let Ok((target, stage)) = self.e.specs.spec(spec).rels.fns[FnRelId(0)] else { return };
        if let Some(intrinsic) = self.e.intrinsic(target) {
          return self.emit_intrinsic_value(span, intrinsic, &args[1], ret);
        }
        if matches!(self.e.specs.spec(target).kind, SpecKind::Synthetic(_)) {
          return self.unsupported("calling a synthetic function value".into());
        }
        let args = args.iter().map(|arg| CallArg::Port(arg.clone())).collect();
        let ret_info = self.port_info(ret);
        let ret = (ret_info.layout.size != 0).then(|| CallRet::Port(ret.clone()));
        self.call(span, CallTarget::Spec(target, stage), args, ret);
      }
      SyntheticItem::EnumDeconstruct(_) => {
        // `Rest(...Rest(Init(content)))`, with as many `Rest`s as the
        // variant's index.
        let info = self.port_info(&args[0]);
        let variants = self.variant_layouts(info.ty);
        let (src, len) = self.read_value(&args[0]);
        self.require(src, len);
        let size = self.port_info(ret).layout.size;
        let out = self.alloc(size);
        let switch = self.code.len();
        self.code.push(Instr::Switch { tag: src, targets: vec![] });
        let mut ends = Vec::new();
        for (index, variant) in variants.iter().enumerate() {
          let label = self.label();
          let Instr::Switch { targets, .. } = &mut self.code[switch] else { unreachable!() };
          targets.push(label);
          let index = index as u32;
          for i in 0..index {
            self.code.push(Instr::Const { dst: out.offset(i), value: 1 });
          }
          self.code.push(Instr::Const { dst: out.offset(index), value: 0 });
          self.code.push(Instr::Move {
            dst: out.offset(index + 1),
            src: src.offset(1),
            len: variant.size,
          });
          for i in index + 1 + variant.size..size {
            self.code.push(Instr::Const { dst: out.offset(i), value: 0 });
          }
          ends.push(self.code.len());
          self.code.push(Instr::Jump { target: Label(0) });
        }
        let end = self.label();
        for index in ends {
          set_target(&mut self.code[index], 0, end);
        }
        self.write_value(ret, out, size);
      }
      SyntheticItem::EnumReconstruct(_) => {
        let info = self.port_info(ret);
        let variants = self.variant_layouts(info.ty);
        let (src, len) = self.read_value(&args[0]);
        self.require(src, len);
        let size = info.layout.size;
        let out = self.alloc(size);
        let mut ends = Vec::new();
        for (index, variant) in variants.iter().enumerate() {
          let index = index as u32;
          let branch = (index + 1 < variants.len() as u32).then(|| {
            // A nonzero tag is `Rest`; the value is a later variant.
            self.code.push(Instr::Branch {
              cond: src.offset(index),
              then: Label(0),
              else_: Label(0),
            });
            let branch = self.code.len() - 1;
            let label = self.label();
            set_target(&mut self.code[branch], 1, label);
            branch
          });
          self.code.push(Instr::Const { dst: out, value: index as u64 });
          self.code.push(Instr::Move {
            dst: out.offset(1),
            src: src.offset(index + 1),
            len: variant.size,
          });
          for i in 1 + variant.size..size {
            self.code.push(Instr::Const { dst: out.offset(i), value: 0 });
          }
          ends.push(self.code.len());
          self.code.push(Instr::Jump { target: Label(0) });
          if let Some(branch) = branch {
            let label = self.label();
            set_target(&mut self.code[branch], 0, label);
          }
        }
        let end = self.label();
        for index in ends {
          set_target(&mut self.code[index], 0, end);
        }
        self.write_value(ret, out, size);
      }
    }
  }

  /// Calls an intrinsic used as a function value, whose parameters are the
  /// fields of a tuple.
  fn emit_intrinsic_value(&mut self, span: Span, intrinsic: Intrinsic, tuple: &Port, ret: &Port) {
    let info = self.port_info(tuple);
    let Some((_, TypeKind::Tuple(tys))) = self.vir.types.kind(info.ty) else { unreachable!() };
    let tys = tys.clone();
    let (reg, _) = self.read_value(tuple);
    // Each parameter becomes the value of a wire of its own.
    let mut params = Vec::new();
    let mut offset = 0;
    for ty in tys {
      let port = Port { ty, kind: PortKind::Wire(Span::NONE, WireId(self.extra_wires)) };
      self.extra_wires -= 1;
      let info = self.port_info(&port);
      if info.writer {
        return self.unsupported("an intrinsic function value with a space parameter".into());
      }
      self.set_wire(info.key.unwrap(), WireState::Value(reg.offset(offset), info.layout.size));
      offset += info.layout.size;
      params.push(port);
    }
    self.emit_intrinsic(span, intrinsic, &params, ret);
  }

  fn variant_layouts(&mut self, ty: Type) -> Vec<Layout> {
    self.e.layouter.variant_layouts_of(&self.vir.types, ty, &self.params).unwrap_or_default()
  }

  fn emit_intrinsic(&mut self, _span: Span, intrinsic: Intrinsic, args: &[Port], ret: &Port) {
    use Intrinsic::*;
    match intrinsic {
      Duplicate | F64Fork => {
        let (value, space) = self.read_ref(&args[0]);
        let copy = self.alloc(value.1);
        self.code.push(Instr::Move { dst: copy, src: value.0, len: value.1 });
        self.write_back(space, value);
        self.write_value(ret, copy, value.1);
      }
      Erase | Forget | F64Drop => self.discard(&args[0]),
      Transmute | BlackBox => {
        let (reg, len) = self.read_value(&args[0]);
        let size = self.port_info(ret).layout.size;
        if size != len {
          // This may be in a branch which is never taken, e.g. of an
          // `IfConst`; it traps if reached.
          self.code.push(Instr::Panic { msg: format!("transmute of {len} words into {size}") });
          let reg = self.alloc(size);
          return self.write_value(ret, reg, size);
        }
        self.write_value(ret, reg, len);
      }
      Unreachable | Panic => {
        let msg = if intrinsic == Unreachable { "unreachable code was reached" } else { "panic" };
        self.code.push(Instr::Panic { msg: msg.into() });
        let size = self.port_info(ret).layout.size;
        let reg = self.alloc(size);
        self.write_value(ret, reg, size);
      }
      IoPrintChar | IoPrintByte | IoFlush | IoReadChar | IoReadByte | IoReady => {
        let op = match intrinsic {
          IoPrintChar => IoOp::PrintChar,
          IoPrintByte => IoOp::PrintByte,
          IoFlush => IoOp::Flush,
          IoReadChar => IoOp::ReadChar,
          IoReadByte => IoOp::ReadByte,
          _ => IoOp::Ready,
        };
        let (io, io_space) = self.read_ref(&args[0]);
        let mut inputs = vec![io.0];
        for arg in &args[1..] {
          let (reg, len) = self.read_value(arg);
          self.require(reg, len);
          inputs.extend((0..len).map(|i| reg.offset(i)));
        }
        let (_, outputs) = op.arity();
        let out = self.alloc(outputs as u32);
        self.require(io.0, 1);
        self.code.push(Instr::Io {
          op,
          args: inputs,
          rets: (0..outputs as u32).map(|i| out.offset(i)).collect(),
        });
        // The new IO handle is the last output.
        self.write_back(io_space, (out.offset(outputs as u32 - 1), 1));
        if outputs > 1 {
          self.write_value(ret, out, 1);
        }
      }
      HoleNew => {
        let ty = self.port_info(ret).ty;
        let size = self.hole_value_size(ty);
        let reg = self.alloc(2);
        self.code.push(Instr::HoleNew { dst: reg, len: size });
        self.code.push(Instr::Space { dst: reg.offset(1), frame: reg, offset: 1 });
        self.write_value(ret, reg, 2);
      }
      HoleOf => {
        let (value, len) = self.read_value(&args[0]);
        self.require(value, len);
        let reg = self.alloc(1);
        self.code.push(Instr::HoleOf { dst: reg, src: value, len });
        self.write_value(ret, reg, 1);
      }
      HoleGet => {
        let (hole, _) = self.read_value(&args[0]);
        self.require(hole, 1);
        let info = self.port_info(ret);
        let len = info.layout.size;
        if !self.wires.contains_key(&info.key.unwrap()) {
          // The value is held by the hole itself.
          let out = self.alloc(len);
          self.hold_regs(hole, (0..len).map(|i| out.offset(i)).collect());
          self.write_value(ret, out, len);
        } else {
          let space = self.wire_space(ret);
          self.materialize(space);
          self.code.push(Instr::HoleForward { hole, space, len });
        }
      }
      HoleForward => {
        let (hole, _) = self.read_value(&args[0]);
        self.require(hole, 1);
        let len = self.port_info(&args[1]).layout.size;
        let space = self.wire_space(&args[1]);
        self.materialize(space);
        self.code.push(Instr::HoleForward { hole, space, len });
      }
      HoleAsRef => {
        // `as_ref(&Hole[T]) -> &T`; the value is borrowed from the hole, and
        // put into a new hole once the borrow ends, which replaces the old one.
        let (hole, hole_space) = self.read_ref(&args[0]);
        self.require(hole.0, 1);
        let size = self.port_info(ret).layout.size;
        let len = size - 1;
        let out = self.alloc(size);
        self.hold_regs(hole.0, (0..len).map(|i| out.offset(i)).collect());
        let new = self.alloc(1);
        self.code.push(Instr::HoleNew { dst: new, len });
        self.code.push(Instr::Space { dst: out.offset(len), frame: new, offset: 1 });
        self.write_back(hole_space, (new, 1));
        self.write_value(ret, out, size);
      }
      _ => {
        let args = args.iter().collect::<Vec<_>>();
        self.emit_op(intrinsic.name(), &args, Some(ret));
      }
    }
  }

  /// Emits a primitive operation, whose arguments may be references (in which
  /// case the value is borrowed).
  fn emit_op(&mut self, name: &'static str, args: &[&Port], ret: Option<&Port>) {
    let mut inputs = Vec::new();
    let mut write_backs = Vec::new();
    for arg in args {
      let info = self.port_info(arg);
      if matches!(self.vir.types.kind(info.ty), Some((_, TypeKind::Ref(_)))) {
        let (value, space) = self.read_ref(arg);
        self.require(value.0, value.1);
        inputs.extend((0..value.1).map(|i| value.0.offset(i)));
        write_backs.push((space, value));
      } else {
        let (reg, len) = self.read_value(arg);
        self.require(reg, len);
        inputs.extend((0..len).map(|i| reg.offset(i)));
      }
    }
    let ret_size = ret.map(|ret| self.port_info(ret).layout.size).unwrap_or(0);
    let out = self.alloc(ret_size);
    let op = self.e.program.op(name);
    self.code.push(Instr::Op {
      op,
      args: inputs,
      rets: (0..ret_size).map(|i| out.offset(i)).collect(),
    });
    for (space, value) in write_backs {
      self.write_back(space, value);
    }
    if let Some(ret) = ret {
      self.write_value(ret, out, ret_size);
    }
  }

  /// The size of an element of a `List` (or of a `String`'s `List`).
  fn list_element_size(&mut self, ty: Type) -> u32 {
    if let Some((_, TypeKind::Struct(_, _, params))) = self.vir.types.kind(ty)
      && let [element] = params[..]
    {
      return self.layout(element).size;
    }
    unreachable!()
  }

  /// Builds a `List`, `(len, Hole[Stream], ~Stream)`, from its parts; a
  /// `Stream` node is a value, followed by a `Hole` for the rest of the
  /// stream.
  fn build_list(&mut self, element_size: u32, parts: Vec<ListPart>) -> Reg {
    // Wait for the parts first, as registers allocated below are not
    // preserved by waiting.
    for part in &parts {
      match *part {
        ListPart::Value((reg, len)) => self.require(reg, len),
        ListPart::List(reg) => self.require(reg, 3),
        ListPart::Char(_) | ListPart::Word(_) => {}
      }
    }
    let node_size = element_size + 1;
    let list = self.alloc(3);
    let mut count = 0;
    let mut lists = Vec::new();
    self.code.push(Instr::HoleNew { dst: list.offset(1), len: node_size });
    let mut tail = self.alloc(1);
    self.code.push(Instr::Space { dst: tail, frame: list.offset(1), offset: 1 });
    for part in parts {
      match part {
        ListPart::Value(_) | ListPart::Char(_) | ListPart::Word(_) => {
          let node = self.alloc(node_size);
          match part {
            ListPart::Value((reg, len)) => self.move_regs(node, reg, len),
            ListPart::Char(c) => self.code.push(Instr::Const { dst: node, value: c as u64 }),
            ListPart::Word(w) => self.code.push(Instr::Const { dst: node, value: w as u64 }),
            ListPart::List(_) => unreachable!(),
          }
          self.code.push(Instr::HoleNew { dst: node.offset(element_size), len: node_size });
          self.emit_write(tail, node, node_size);
          tail = self.alloc(1);
          self.code.push(Instr::Space { dst: tail, frame: node.offset(element_size), offset: 1 });
          count += 1;
        }
        ListPart::List(other) => {
          // Splice in another list: forward its front into the tail, and
          // continue from its back.
          self.code.push(Instr::HoleForward { hole: other.offset(1), space: tail, len: node_size });
          lists.push(other);
          tail = other.offset(2);
        }
      }
    }
    self.code.push(Instr::Const { dst: list, value: count });
    if !lists.is_empty() {
      let add = self.e.program.op("n32:add");
      for other in lists {
        self.code.push(Instr::Op { op: add, args: vec![list, other], rets: vec![list] });
      }
    }
    self.code.push(Instr::Move { dst: list.offset(2), src: tail, len: 1 });
    list
  }

  fn hole_value_size(&mut self, ty: Type) -> u32 {
    // `(Hole[T], ~T)`
    if let Some((_, TypeKind::Tuple(tys))) = self.vir.types.kind(ty)
      && let Some((_, TypeKind::Opaque(_, params))) = self.vir.types.kind(tys[0])
    {
      return self.layout(params[0]).size;
    }
    unreachable!()
  }

  /// Reads a reference, returning the registers of its value, and of its
  /// space.
  fn read_ref(&mut self, port: &Port) -> ((Reg, u32), Reg) {
    let (reg, len) = self.read_value(port);
    ((reg, len - 1), reg.offset(len - 1))
  }

  /// Writes a borrowed value back into the reference's space.
  fn write_back(&mut self, space: Reg, (reg, len): (Reg, u32)) {
    self.emit_write(space, reg, len);
  }

  // Composites

  fn emit_composite(&mut self, port: &Port, fields: &[Port]) {
    let info = self.port_info(port);
    let fields = fields.iter().map(|f| (f, self.port_info(f))).collect::<Vec<_>>();
    // A field is part of the composite's value if it flows the other way; if
    // it flows the same way, the composite contains a space for it instead.
    let sizes = fields
      .iter()
      .map(|(_, f)| if f.writer == info.writer { 1 } else { f.layout.size })
      .map(|size| size.min(info.layout.size))
      .collect::<Vec<_>>();
    if info.writer {
      let reg = self.alloc(info.layout.size);
      let mut offset = 0;
      for ((field, field_info), &size) in fields.iter().zip(&sizes) {
        if field_info.layout.size == 0 {
          continue;
        }
        if field_info.writer {
          let space = self.wire_space(field);
          self.move_regs(reg.offset(offset), space, 1);
          offset += 1;
        } else {
          let (src, len) = self.read_value(field);
          self.move_regs(reg.offset(offset), src, len);
          offset += size;
        }
      }
      // E.g. the space of a reference to an empty value, which is never
      // written through.
      for i in offset..info.layout.size {
        self.code.push(Instr::Const { dst: reg.offset(i), value: 0 });
      }
      self.write_value(port, reg, info.layout.size);
    } else {
      let (reg, _) = self.read_value(port);
      let mut offset = 0;
      for ((field, field_info), _) in fields.iter().zip(&sizes) {
        if field_info.layout.size == 0 {
          continue;
        }
        if field_info.writer {
          self.write_value(field, reg.offset(offset), field_info.layout.size);
          offset += field_info.layout.size;
        } else {
          self.wire_reader_space(field, reg.offset(offset));
          offset += 1;
        }
      }
    }
  }

  /// A reference is its value, followed by a space for its value afterwards.
  fn emit_ref(&mut self, reference: &Port, value: &Port, space: &Port) {
    let info = self.port_info(reference);
    let space_info = self.port_info(space);
    if space_info.writer == info.writer || space_info.layout.size == 0 {
      return self.emit_composite(reference, &[value.clone(), space.clone()]);
    }
    // The referenced type is itself a space, `~T`; the space port carries a
    // `T`, while the reference's last word is a space for a space for a `T`.
    let len = space_info.layout.size;
    if info.writer {
      let reg = self.alloc(2);
      let value_space = self.wire_space(value);
      self.move_regs(reg, value_space, 1);
      let (src, src_len) = self.read_value(space);
      if self.virtual_run(src, src_len) == Some(len) {
        // The `T` is written through a virtual space; the space it is written
        // through will be written into the reference's space instead.
        let (virtual_space, _) = self.unwritten[&src];
        for i in 0..len {
          self.unwritten.remove(&src.offset(i));
        }
        self.virtual_spaces.remove(&virtual_space);
        let space = self.pending_space(virtual_space, 1);
        self.move_regs(reg.offset(1), space, 1);
      } else {
        // Once the space is written, write the `T` into it.
        self.require_filled(src, src_len);
        let block = self.e.write_block(len);
        let frame = self.alloc(1);
        self.code.push(Instr::NewFrame { dst: frame, block });
        self.emit_fill(frame, 2, src, len);
        self.code.push(Instr::Space { dst: reg.offset(1), frame, offset: 1 });
      }
      self.write_value(reference, reg, 2);
    } else {
      let (reg, _) = self.read_value(reference);
      self.wire_reader_space(value, reg);
      // Write a space for the `T` into the reference's space.
      let out = self.alloc(len);
      let out_space = self.pending_space(out, len);
      self.emit_write(reg.offset(1), out_space, 1);
      self.write_value(space, out, len);
    }
  }

  fn emit_link(&mut self, a: &Port, b: &Port) {
    let (writer, reader) = if self.writes_first(a, b) { (a, b) } else { (b, a) };
    let info = self.port_info(writer);
    if info.layout.size == 0 {
      // E.g. matching a union on an empty variant; the value is discarded.
      if self.port_info(reader).layout.size != 0 {
        self.discard(reader);
      }
      return;
    }
    let reader_info = self.port_info(reader);
    if self.boxes(info.ty, reader_info.ty) {
      return self.emit_box(writer, reader);
    }
    if self.boxes(reader_info.ty, info.ty) {
      return self.emit_unbox(writer, reader);
    }
    // A `Rewrap` may change the layout, e.g. between a union and one of its
    // variants; then the value is padded or truncated.
    let same = reader_info.layout.size == info.layout.size;
    if same
      && let Some(key) = reader_info.key
      && let Some(WireState::LocalAtEnd(local)) = self.wires.get(&key).copied()
    {
      self.wires.insert(key, WireState::Consumed);
      let writer_key = info.key.unwrap();
      let state = match self.wires.get(&writer_key).copied() {
        Some(WireState::ReaderSpace(space)) => {
          self.at_end.push((local, AtEnd::Write(space)));
          WireState::Consumed
        }
        Some(WireState::ReaderLocal(other)) => {
          self.set_at_end(other, local);
          WireState::Consumed
        }
        None => WireState::LocalAtEnd(local),
        _ => {
          self.unsupported("a value used before it is computed".into());
          WireState::Consumed
        }
      };
      self.wires.insert(writer_key, state);
      return;
    }
    if same
      && let Some(key) = reader_info.key
      && !self.wires.contains_key(&key)
    {
      // The value has not been produced yet; it will flow to the writer's
      // reader.
      match self.wires.get(&info.key.unwrap()).copied() {
        Some(WireState::ReaderSpace(space)) => {
          self.wires.insert(key, WireState::ReaderSpace(space));
        }
        Some(WireState::ReaderLocal(local)) => {
          self.wires.insert(key, WireState::ReaderLocal(local));
          self.locals[local] = LocalState::Alias(key);
        }
        _ => self.unsupported("a value used before it is computed".into()),
      }
      self.wires.insert(info.key.unwrap(), WireState::Consumed);
      return;
    }
    let (reg, len) = self.read_value(reader);
    let size = info.layout.size;
    if len < size {
      let padded = self.alloc(size);
      self.move_regs(padded, reg, len);
      for i in len..size {
        self.code.push(Instr::Const { dst: padded.offset(i), value: 0 });
      }
      self.write_value(writer, padded, size);
    } else {
      self.write_value(writer, reg, size);
    }
  }

  /// Whether `outer` is `Box[inner]`.
  fn boxes(&self, outer: Type, inner: Type) -> bool {
    let box_ = self.e.chart.builtins.box_;
    let types = &self.vir.types;
    match types.kind(outer) {
      Some((_, TypeKind::Struct(id, _, params))) if Some(*id) == box_ => {
        types.show(self.e.chart, params[0]) == types.show(self.e.chart, inner)
      }
      _ => false,
    }
  }

  /// Boxes a value: a box is a hole holding its contents.
  fn emit_box(&mut self, writer: &Port, reader: &Port) {
    let info = self.port_info(reader);
    let len = info.layout.size;
    let hole = match info.key {
      Some(key) if len != 0 && !self.wires.contains_key(&key) => {
        // The contents are produced later; they are written into the hole.
        let hole = self.alloc(1);
        self.code.push(Instr::HoleNew { dst: hole, len });
        let space = self.alloc(1);
        self.code.push(Instr::Space { dst: space, frame: hole, offset: 1 });
        self.wire_reader_space(reader, space);
        hole
      }
      _ => {
        let (reg, len) = self.read_value(reader);
        self.hole_holding(reg, len)
      }
    };
    self.write_value(writer, hole, 1);
  }

  /// Unboxes a value; the contents are held by the box's hole.
  fn emit_unbox(&mut self, writer: &Port, reader: &Port) {
    let (handle, _) = self.read_value(reader);
    let len = self.port_info(writer).layout.size;
    let out = self.alloc(len);
    let hole = if self.remote(handle, 1) {
      // The box is not available yet; a task forwards its contents into a
      // new hole once it is.
      let hole = self.alloc(1);
      self.code.push(Instr::HoleNew { dst: hole, len });
      let space = self.alloc(1);
      self.code.push(Instr::Space { dst: space, frame: hole, offset: 1 });
      let mut task = self.new_task();
      let handle = self.task_input(&mut task, handle, 1);
      let space = self.task_input(&mut task, space, 1);
      task.code.push(Instr::HoleForward { hole: handle, space, len });
      self.finish_task(task);
      hole
    } else {
      handle
    };
    self.hold_regs(hole, (0..len).map(|i| out.offset(i)).collect());
    if len == 0 {
      self.discard_held_hole(hole, 0);
    }
    self.write_value(writer, out, len);
  }

  /// Of two ports connected by a step, whether the first one is the writer.
  /// If neither carries a space, the writer is the inverted one; e.g. a value
  /// of a self-inverse type, like `()`, rewrapped as a union.
  fn writes_first(&mut self, a: &Port, b: &Port) -> bool {
    match (self.port_info(a).writer, self.port_info(b).writer) {
      (true, _) => true,
      (false, true) => false,
      (false, false) => matches!(self.vir.types.kind(a.ty), Some((inv, _)) if inv.0),
    }
  }

  // Wires

  fn port_info(&mut self, port: &Port) -> PortInfo {
    let types = &self.vir.types;
    let writer =
      matches!(types.kind(port.ty), Some((inv, _)) if inv.0) && !types.self_inverse(port.ty);
    let ty = if writer { port.ty.inverse() } else { port.ty };
    let layout = self.layout(ty);
    let key = match port.kind {
      PortKind::Wire(_, wire) => Some((self.stage, wire)),
      _ => None,
    };
    PortInfo { key, writer, ty, layout }
  }

  fn layout(&mut self, ty: Type) -> Layout {
    match self.e.layout(&self.vir.types, ty, &self.params) {
      Ok(layout) => layout,
      Err(_) => Layout { size: 0, plain: true },
    }
  }

  fn set_wire(&mut self, key: WireKey, state: WireState) {
    self.wires.insert(key, state);
  }

  /// Reads a port's value (as its reader), returning the registers holding it;
  /// they may be pending.
  fn read_value(&mut self, port: &Port) -> (Reg, u32) {
    let info = self.port_info(port);
    let size = info.layout.size;
    let Some(key) = info.key else {
      if let PortKind::Nat(nat) = &port.kind {
        // A `Nat` is a list of its 32-bit digits, least significant first.
        let list = self.build_list(1, nat.0.iter().map(|&digit| ListPart::Word(digit)).collect());
        self.temps.push((list, 3));
        return (list, 3);
      }
      let words: Vec<u64> = match &port.kind {
        PortKind::Nil | PortKind::Error(_) => vec![0; size as usize],
        PortKind::Bool(b) => vec![*b as u64],
        PortKind::N32(n) => vec![*n as u64],
        PortKind::F32(f) => vec![f.to_bits() as u64],
        PortKind::F64(f) => vec![f.to_bits()],
        PortKind::Nat(_) | PortKind::Wire(..) => unreachable!(),
      };
      let reg = self.alloc(words.len() as u32);
      for (i, word) in words.into_iter().enumerate() {
        self.code.push(Instr::Const { dst: reg.offset(i as u32), value: word });
      }
      self.temps.push((reg, size));
      return (reg, size);
    };
    if size == 0 {
      self.wires.insert(key, WireState::Consumed);
      return (Reg(0), 0);
    }
    match self.wires.get(&key).copied() {
      Some(WireState::Value(reg, len)) => {
        self.wires.insert(key, WireState::Consumed);
        self.temps.push((reg, len));
        (reg, len)
      }
      Some(WireState::LocalAtEnd(local)) => {
        self.wires.insert(key, WireState::Consumed);
        if self.is_final(local) {
          let (reg, len) = self.local_value(local);
          self.locals[local] = LocalState::Empty;
          self.temps.push((reg, len));
          (reg, len)
        } else {
          // The local's final value will be written into these registers.
          let reg = self.alloc(size);
          let space = self.pending_space(reg, size);
          self.at_end.push((local, AtEnd::Write(space)));
          (reg, size)
        }
      }
      _ => {
        self.unsupported("a value used before it is computed".into());
        (self.alloc(size), size)
      }
    }
  }

  /// Discards a port's value (as its reader).
  fn discard(&mut self, port: &Port) {
    let info = self.port_info(port);
    match info.key {
      Some(key) if info.layout.size != 0 && !self.wires.contains_key(&key) => {
        self.wires.insert(key, WireState::Discard);
      }
      _ => {
        let (reg, len) = self.read_value(port);
        self.discard_held(reg, len);
      }
    }
  }

  /// Reads a port's value (as its reader) by writing it into `space`, once it
  /// has been produced.
  fn read_into_space(&mut self, port: &Port, space: Reg) {
    let info = self.port_info(port);
    let Some(key) = info.key else {
      let (reg, len) = self.read_value(port);
      self.emit_write(space, reg, len);
      return;
    };
    if info.layout.size == 0 {
      return;
    }
    match self.wires.get(&key).copied() {
      None => self.wire_reader_space(port, space),
      Some(WireState::LocalAtEnd(local)) => {
        self.wires.insert(key, WireState::Consumed);
        self.at_end.push((local, AtEnd::Write(space)));
      }
      Some(_) => {
        let (reg, len) = self.read_value(port);
        self.emit_write(space, reg, len);
      }
    }
  }

  /// Records that the port's value (as its reader) must be written into
  /// `space`.
  fn wire_reader_space(&mut self, port: &Port, space: Reg) {
    let info = self.port_info(port);
    let Some(key) = info.key else {
      let (reg, len) = self.read_value(port);
      self.emit_write(space, reg, len);
      return;
    };
    if info.layout.size == 0 {
      return;
    }
    match self.wires.get(&key).copied() {
      None => {
        self.wires.insert(key, WireState::ReaderSpace(space));
      }
      Some(_) => self.read_into_space(port, space),
    }
  }

  /// Produces a port's value (as its writer) in registers.
  fn write_value(&mut self, port: &Port, reg: Reg, len: u32) {
    let info = self.port_info(port);
    let Some(key) = info.key else { return };
    if info.layout.size == 0 {
      return;
    }
    match self.wires.get(&key).copied() {
      None => {
        self.wires.insert(key, WireState::Value(reg, len));
      }
      Some(WireState::ReaderLocal(local)) => {
        let regs = self.local_regs(local);
        self.move_regs(regs.0, reg, len);
        self.locals[local] = LocalState::Valid;
        self.wires.insert(key, WireState::Consumed);
      }
      Some(WireState::ReaderSpace(space)) => {
        self.emit_write(space, reg, len);
        self.wires.insert(key, WireState::Consumed);
      }
      Some(WireState::Discard) => {
        self.wires.insert(key, WireState::Consumed);
        // Holes holding the value are still read, to free them.
        self.discard_held(reg, len);
      }
      Some(state) => {
        unreachable!(
          "{key:?} is {state:?} in {} ({:?}, step {})",
          self.fragment.path, self.stage, self.step
        )
      }
    }
  }

  /// Produces a port's value (as its writer) by returning a space it will be
  /// written into later.
  fn wire_space(&mut self, port: &Port) -> Reg {
    let info = self.port_info(port);
    let len = info.layout.size;
    let key = info.key.unwrap();
    match self.wires.get(&key).copied() {
      None => {
        let reg = self.alloc(len);
        let space = self.pending_space(reg, len);
        if self.awaited_by_transfer(key.1, self.step) {
          // The next transfer waits for it anyway, so it arrives where the
          // transfer waits, rather than in a hole.
          self.materialize_cont(space);
        } else if let Some(reader) = self.strict_reader(key.1, self.step) {
          // The step reading it will be emitted into a task; the value is
          // written directly into the task's frame, and the step is emitted
          // into it (see `task_of`).
          let task = match self.reader_tasks.get(&reader) {
            Some(&task) => task,
            None => {
              let task = self.new_task();
              self.open_tasks.push(task);
              self.reader_tasks.insert(reader, self.open_tasks.len() - 1);
              self.open_tasks.len() - 1
            }
          };
          self.take_virtual(reg, len);
          let (frame, offset) = (self.open_tasks[task].frame, self.open_tasks[task].offset());
          self.code.push(Instr::Space { dst: space, frame, offset });
          self.open_tasks[task].map.extend((0..len).map(|i| reg.offset(i)));
          for i in 0..len {
            self.in_task.insert(reg.offset(i), (task, reg.offset(i)));
          }
        }
        self.wires.insert(key, WireState::Value(reg, len));
        space
      }
      Some(WireState::ReaderLocal(local)) => {
        let (reg, _) = self.local_regs(local);
        let space = self.pending_space(reg, len);
        self.locals[local] = LocalState::Valid;
        self.wires.insert(key, WireState::Consumed);
        space
      }
      Some(WireState::ReaderSpace(space)) => {
        self.wires.insert(key, WireState::Consumed);
        space
      }
      Some(WireState::Discard) => {
        self.wires.insert(key, WireState::Consumed);
        self.null_space()
      }
      Some(state) => unreachable!("{} {key:?} {state:?}", self.fragment.path),
    }
  }

  /// Whether the value of a wire, produced by the step at `from`, is only
  /// moved (through locals) to the data of the next transfer of the stage.
  fn awaited_by_transfer(&self, wire: WireId, from: usize) -> bool {
    let stage = &self.vir.stages[self.stage];
    let is_wire = |port: &Port, w: WireId| matches!(port.kind, PortKind::Wire(_, x) if x == w);
    let mut wire = wire;
    let mut index = from;
    for _ in 0..8 {
      let Some((i, step)) = stage.steps.iter().enumerate().skip(index + 1).find(|(_, step)| {
        matches!(step, Step::Transfer(_)) || step.ports().any(|p| is_wire(p, wire))
      }) else {
        return false;
      };
      match step {
        Step::Transfer(transfer) => {
          return transfer.data.as_ref().is_some_and(|data| is_wire(data, wire))
            && !creates_value(&self.vir.interfaces[transfer.interface].kind);
        }
        Step::Invoke(_, local, Invocation::Write(p) | Invocation::BarrierWrite(p))
          if is_wire(p, wire) =>
        {
          // Follow the local to where it is read next, if before a transfer.
          let next = stage.steps.iter().enumerate().skip(i + 1).find(|(_, step)| match step {
            Step::Invoke(_, l, _) => l == local,
            Step::Transfer(_) => true,
            _ => false,
          });
          let Some((j, Step::Invoke(_, _, Invocation::ReadBarrier(p)))) = next else {
            return false;
          };
          let PortKind::Wire(_, w) = p.kind else { return false };
          (wire, index) = (w, j);
        }
        _ => return false,
      }
    }
    false
  }

  // Registers and waiting

  fn alloc(&mut self, len: u32) -> Reg {
    let reg = Reg(self.next_reg);
    self.next_reg += len;
    reg
  }

  fn label(&self) -> Label {
    Label(self.code.len() as u32)
  }

  /// Returns a (virtual) space for `len` words, which will be written into
  /// `reg`.
  fn pending_space(&mut self, reg: Reg, len: u32) -> Reg {
    let space = self.alloc(1);
    for i in 0..len {
      self.unwritten.insert(reg.offset(i), (space, i as usize));
    }
    self.virtual_spaces.insert(space, (0..len).map(|i| reg.offset(i)).collect());
    space
  }

  /// Makes a virtual space real, as it escapes the unit: its value is held by a
  /// hole, so that only code which reads it waits for it.
  fn materialize(&mut self, space: Reg) {
    if self.virtual_spaces.contains_key(&space) {
      self.hold(space);
    }
  }

  /// Makes a virtual space real, pointing into a new hole, which holds its
  /// value.
  fn hold(&mut self, space: Reg) {
    let targets = self.virtual_spaces.remove(&space).unwrap();
    for target in &targets {
      self.unwritten.remove(target);
    }
    let hole = self.alloc(1);
    self.code.push(Instr::HoleNew { dst: hole, len: targets.len() as u32 });
    self.code.push(Instr::Space { dst: space, frame: hole, offset: 1 });
    self.hold_regs(hole, targets);
  }

  /// Records that the hole in `hole` holds the values of `targets`.
  fn hold_regs(&mut self, hole: Reg, targets: Vec<Reg>) {
    for (i, &target) in targets.iter().enumerate() {
      self.held.insert(target, (hole, i));
    }
    self.holes.insert(hole, targets);
  }

  /// Reads the holes holding any of the given registers; their values will
  /// arrive in the continuation frame.
  fn resolve(&mut self, reg: Reg, len: u32) {
    self.release(reg, len);
    for i in 0..len {
      if let Some(&(hole, _)) = self.held.get(&reg.offset(i)) {
        let targets = self.holes.remove(&hole).unwrap();
        for target in &targets {
          self.held.remove(target);
        }
        let len = targets.len() as u32;
        let space = self.alloc(1);
        for (i, &target) in targets.iter().enumerate() {
          self.unwritten.insert(target, (space, i));
        }
        self.virtual_spaces.insert(space, targets);
        self.materialize_cont(space);
        self.code.push(Instr::HoleForward { hole, space, len });
      }
    }
  }

  /// Returns a register holding a hole which holds the values of the given
  /// registers.
  fn hole_holding(&mut self, reg: Reg, len: u32) -> Reg {
    self.align_holes(reg, len);
    match self.runs(reg, len)[..] {
      [] => {
        let hole = self.alloc(1);
        self.code.push(Instr::HoleOf { dst: hole, src: reg, len: 0 });
        hole
      }
      [(0, run_len, Run::Held)] if run_len == len => self.take_held(reg, len),
      [(0, run_len, Run::Task(_))] if run_len == len => {
        self.release(reg, len);
        self.take_held(reg, len)
      }
      [(0, run_len, Run::Virtual)] if run_len == len => {
        let (space, _) = self.unwritten[&reg];
        self.hold(space);
        self.take_held(reg, len)
      }
      [(0, _, Run::Real)] if !self.remote(reg, len) => {
        self.materialize_range(reg, len);
        let hole = self.alloc(1);
        self.code.push(Instr::HoleOf { dst: hole, src: reg, len });
        hole
      }
      _ => {
        // Parts of the value are not available yet; they are written into the
        // hole once they are.
        let hole = self.alloc(1);
        self.code.push(Instr::HoleNew { dst: hole, len });
        let space = self.alloc(1);
        self.code.push(Instr::Space { dst: space, frame: hole, offset: 1 });
        self.emit_write(space, reg, len);
        hole
      }
    }
  }

  /// Whether any of the registers' values are not available yet.
  fn remote(&self, reg: Reg, len: u32) -> bool {
    (0..len).map(|i| reg.offset(i)).any(|r| {
      self.held.contains_key(&r)
        || self.unwritten.contains_key(&r)
        || self.pending.contains_key(&r)
        || self.in_task.contains_key(&r)
    })
  }

  /// Splits the holes holding some of the given registers, and some other
  /// registers, so that each hole holds either only registers within the
  /// range, or none; e.g. when a field of a value held by a hole is passed on
  /// separately. A task receives the hole's value, and writes its parts into
  /// new holes.
  fn align_holes(&mut self, reg: Reg, len: u32) {
    let inside = |r: Reg| r >= reg && r < reg.offset(len);
    // A virtual space for only part of the range, or for registers outside of
    // it, is made real first.
    for i in 0..len {
      if let Some(&(space, _)) = self.unwritten.get(&reg.offset(i)) {
        let targets = &self.virtual_spaces[&space];
        let first = targets[0];
        let aligned = inside(first)
          && inside(first.offset(targets.len() as u32 - 1))
          && targets.iter().enumerate().all(|(j, &t)| t == first.offset(j as u32));
        if !aligned {
          self.hold(space);
        }
      }
    }
    for i in 0..len {
      let Some(&(hole, _)) = self.held.get(&reg.offset(i)) else { continue };
      let targets = self.holes[&hole].clone();
      let mut groups: Vec<Vec<Reg>> = Vec::new();
      for &target in &targets {
        match groups.last_mut() {
          Some(group)
            if *group.last().unwrap() == Reg(target.0.wrapping_sub(1))
              && inside(target) == inside(group[0]) =>
          {
            group.push(target)
          }
          _ => groups.push(vec![target]),
        }
      }
      if groups.len() == 1 {
        continue;
      }
      self.holes.remove(&hole);
      for target in &targets {
        self.held.remove(target);
      }
      let mut task = self.new_task();
      let value = self.alloc(targets.len() as u32);
      let space = self.alloc(1);
      self.code.push(Instr::Space { dst: space, frame: task.frame, offset: 1 });
      self.code.push(Instr::HoleForward { hole, space, len: targets.len() as u32 });
      task.map.extend((0..targets.len() as u32).map(|i| value.offset(i)));
      let mut offset = 0;
      for group in groups {
        let len = group.len() as u32;
        let space = self.task_output(&mut task, group[0], len);
        task.code.push(Instr::Write { space, src: value.offset(offset), len });
        offset += len;
      }
      self.finish_task(task);
    }
  }

  // Tasks

  /// Creates a task, whose frame is filled by the code being emitted.
  fn new_task(&mut self) -> Task {
    let frame = self.alloc(1);
    let block =
      self.e.program.blocks.push(Block { unit: self.unit, entry: Label(0), frame: vec![] });
    self.code.push(Instr::NewFrame { dst: frame, block });
    Task { frame, block, map: Vec::new(), code: Vec::new() }
  }

  /// Passes a value to a task, returning the registers it is loaded into.
  fn task_input(&mut self, task: &mut Task, reg: Reg, len: u32) -> Reg {
    let dst = self.alloc(len);
    self.emit_fill(task.frame, task.offset(), reg, len);
    task.map.extend((0..len).map(|i| dst.offset(i)));
    dst
  }

  /// Passes a space to a task, through which it writes the value of the given
  /// registers; returns the register the space is loaded into. The registers'
  /// values are held by a hole until then.
  fn task_output(&mut self, task: &mut Task, reg: Reg, len: u32) -> Reg {
    let space = self.pending_space(reg, len);
    self.task_input(task, space, 1)
  }

  /// Finishes a task; its code is placed after the unit's other code.
  fn finish_task(&mut self, mut task: Task) {
    task.code.push(Instr::End);
    self.tasks.push(task);
  }

  /// Whether a step needs values which are not available yet. Such a step is
  /// emitted into a task of its own, so that only it waits for them.
  fn waits(&mut self, step: &Step) -> bool {
    let inputs = self.strict_inputs(step);
    inputs.into_iter().any(|port| self.port_waits(port))
  }

  /// The ports whose values a step reads, rather than only passes on; empty if
  /// it reads none.
  fn strict_inputs<'s>(&self, step: &'s Step) -> Vec<&'s Port> {
    match step {
      Step::Call(_, rel, args, _) => {
        let Ok((callee, _)) = self.e.specs.spec(self.spec_id).rels.fns[*rel] else {
          return vec![];
        };
        let strict = match self.e.intrinsic(callee) {
          Some(intrinsic) => reads_inputs(intrinsic),
          None => match &self.e.specs.spec(callee).kind {
            SpecKind::Synthetic(
              SyntheticItem::EnumDeconstruct(_) | SyntheticItem::EnumReconstruct(_),
            ) => true,
            SpecKind::Synthetic(SyntheticItem::CallFn(..)) => {
              match self.e.specs.spec(callee).rels.fns[FnRelId(0)] {
                Ok((target, _)) => self.e.intrinsic(target).is_some_and(reads_inputs),
                Err(_) => false,
              }
            }
            _ => false,
          },
        };
        if !strict {
          return vec![];
        }
        args.iter().collect()
      }
      Step::List(_, elements) => elements.iter().collect(),
      Step::String(_, _, rest) => rest.iter().map(|(port, _)| port).collect(),
      Step::BoolNot(a, _) => vec![a],
      Step::BoolAnd(a, b, _) => vec![a, b],
      _ => vec![],
    }
  }

  /// If the value of a wire, produced by the step at `from`, is read by a
  /// step before the next transfer, which then waits for it, returns the
  /// index of that step.
  fn strict_reader(&self, wire: WireId, from: usize) -> Option<usize> {
    let stage = &self.vir.stages[self.stage];
    let is_wire = |port: &Port| matches!(port.kind, PortKind::Wire(_, w) if w == wire);
    let (index, step) = stage
      .steps
      .iter()
      .enumerate()
      .skip(from + 1)
      .find(|(_, step)| matches!(step, Step::Transfer(_)) || step.ports().any(is_wire))?;
    self.strict_inputs(step).into_iter().any(is_wire).then_some(index)
  }

  /// Whether the value of a port read by a step is not available yet.
  fn port_waits(&mut self, port: &Port) -> bool {
    let info = self.port_info(port);
    let Some(key) = info.key else { return false };
    if info.writer || info.layout.size == 0 {
      return false;
    }
    match self.wires.get(&key).copied() {
      None => true,
      Some(WireState::Value(reg, len)) => self.remote(reg, len),
      Some(WireState::LocalAtEnd(local)) => !self.is_final(local) || self.local_waits(local),
      Some(_) => false,
    }
  }

  /// Whether the value of a local is not available yet.
  fn local_waits(&self, local: Local) -> bool {
    match self.locals[local] {
      LocalState::Empty => false,
      LocalState::Valid => {
        self.local_regs.get(&local).is_some_and(|&(reg, len)| self.remote(reg, len))
      }
      LocalState::Alias(key) => match self.wires.get(&key) {
        Some(&WireState::Value(reg, len)) => self.remote(reg, len),
        _ => true,
      },
      LocalState::AtEnd(_) => true,
    }
  }

  /// Emits a step which needs values that are not available yet into a task:
  /// the task receives the values the step reads, and spaces for the values it
  /// writes, and runs the step once they have all arrived. The code emitting it
  /// goes on without waiting.
  ///
  /// If all the values the step waits for are computed by one open task, the
  /// step is emitted into that task, which waits for nothing more as a result.
  /// Values the step computes stay in the task, until they are used elsewhere.
  fn emit_detached(&mut self, index: usize, step: &Step) {
    let echoes = self.is_op(step);
    let keeps = echoes
      || matches!(step, Step::List(..) | Step::String(..) | Step::BoolNot(..) | Step::BoolAnd(..));
    let task = match self.task_of(step) {
      Some(task) => task,
      None => {
        let task = self.new_task();
        self.open_tasks.push(task);
        self.open_tasks.len() - 1
      }
    };
    let frame = self.open_tasks[task].frame;
    let mut flow = Flow::default();
    let mut outputs = Vec::new();
    for port in step.ports() {
      let info = self.port_info(port);
      let Some(key) = info.key else { continue };
      let len = info.layout.size;
      if len == 0 {
        continue;
      }
      if info.writer {
        if keeps && !self.wires.contains_key(&key) {
          outputs.push(key);
          continue;
        }
        let space = self.wire_space(port);
        let reg = self.open_task_input(task, space, 1);
        flow.wires.insert(key, WireState::ReaderSpace(reg));
      } else if !self.wires.contains_key(&key) {
        // The value is produced later by this stage; it is written directly
        // into the task's frame.
        let space = self.alloc(1);
        let offset = self.open_tasks[task].offset();
        self.code.push(Instr::Space { dst: space, frame, offset });
        self.wire_reader_space(port, space);
        let reg = self.alloc(len);
        self.open_tasks[task].map.extend((0..len).map(|i| reg.offset(i)));
        flow.wires.insert(key, WireState::Value(reg, len));
      } else if echoes && self.is_ref(info.ty) {
        // An operation only reads the value behind a reference, and writes it
        // back unchanged. It is written back now, so that values which depend
        // on it (e.g. another reference to the same local) need not wait for
        // the task; the task gets a copy, and writes back into nothing.
        let (src, len) = self.read_value(port);
        let (space, len) = (src.offset(len - 1), len - 1);
        let reg = self.alloc(len + 1);
        if (0..len).all(|i| self.in_task.get(&src.offset(i)).is_some_and(|x| x.0 == task)) {
          let value = self.task_regs(task, src, len, false);
          self.open_tasks[task].code.push(Instr::Move { dst: reg, src: value, len });
          self.emit_write(space, src, len);
        } else {
          let copy = self.alloc(len);
          self.duplicate(src, len, copy);
          self.emit_write(space, src, len);
          let offset = self.open_tasks[task].offset();
          self.emit_fill(frame, offset, copy, len);
          self.open_tasks[task].map.extend((0..len).map(|i| reg.offset(i)));
        }
        let unused = self.alloc(len);
        for i in 0..len {
          flow.unwritten.insert(unused.offset(i), (reg.offset(len), i as usize));
        }
        flow.virtual_spaces.insert(reg.offset(len), (0..len).map(|i| unused.offset(i)).collect());
        flow.wires.insert(key, WireState::Value(reg, len + 1));
      } else {
        let (src, len) = self.read_value(port);
        let reg = self.open_task_input(task, src, len);
        flow.wires.insert(key, WireState::Value(reg, len));
      }
    }
    // The step's code is emitted with the task's own state, where all of its
    // values are available.
    flow.code = take(&mut self.open_tasks[task].code);
    self.swap_flow(&mut flow);
    self.emit_step(index, step);
    self.swap_flow(&mut flow);
    debug_assert!(flow.pending.is_empty() && flow.virtual_spaces.is_empty());
    self.open_tasks[task].code = take(&mut flow.code);
    for key in outputs {
      if let Some(&WireState::Value(reg, len)) = flow.wires.get(&key) {
        for i in 0..len {
          self.in_task.insert(reg.offset(i), (task, reg.offset(i)));
        }
        self.set_wire(key, WireState::Value(reg, len));
      }
    }
  }

  /// Passes a value to an open task, returning the registers it is loaded
  /// into; parts of it the task computes itself are just moved there.
  fn open_task_input(&mut self, task: usize, reg: Reg, len: u32) -> Reg {
    if let [(0, run_len, Run::Task(t))] = self.runs(reg, len)[..]
      && run_len == len
      && t == task
    {
      return self.task_regs(task, reg, len, true);
    }
    let dst = self.alloc(len);
    self.align_holes(reg, len);
    for (start, run_len, kind) in self.runs(reg, len) {
      let (src, dst) = (reg.offset(start), dst.offset(start));
      if kind == Run::Task(task) {
        let value = self.task_regs(task, src, run_len, true);
        let code = &mut self.open_tasks[task].code;
        code.push(Instr::Move { dst, src: value, len: run_len });
      } else {
        let (frame, offset) = (self.open_tasks[task].frame, self.open_tasks[task].offset());
        self.emit_fill(frame, offset, src, run_len);
        self.open_tasks[task].map.extend((0..run_len).map(|i| dst.offset(i)));
      }
    }
    dst
  }

  /// Whether a step is a primitive operation (see `emit_op`).
  fn is_op(&self, step: &Step) -> bool {
    let Step::Call(_, rel, _, _) = step else { return false };
    let Ok((callee, _)) = self.e.specs.spec(self.spec_id).rels.fns[*rel] else { return false };
    self.e.intrinsic(callee).is_some_and(|intrinsic| {
      use Intrinsic::*;
      !matches!(
        intrinsic,
        Duplicate
          | F64Fork
          | Erase
          | Forget
          | F64Drop
          | Transmute
          | BlackBox
          | Unreachable
          | Panic
          | IoPrintChar
          | IoPrintByte
          | IoFlush
          | IoReadChar
          | IoReadByte
          | IoReady
          | HoleNew
          | HoleOf
          | HoleGet
          | HoleForward
          | HoleAsRef
      )
    })
  }

  fn is_ref(&self, ty: Type) -> bool {
    matches!(self.vir.types.kind(ty), Some((_, TypeKind::Ref(_))))
  }

  fn swap_flow(&mut self, flow: &mut Flow) {
    swap(&mut self.code, &mut flow.code);
    swap(&mut self.wires, &mut flow.wires);
    swap(&mut self.pending, &mut flow.pending);
    swap(&mut self.cont, &mut flow.cont);
    swap(&mut self.virtual_spaces, &mut flow.virtual_spaces);
    swap(&mut self.unwritten, &mut flow.unwritten);
    swap(&mut self.held, &mut flow.held);
    swap(&mut self.holes, &mut flow.holes);
    swap(&mut self.in_task, &mut flow.in_task);
    swap(&mut self.temps, &mut flow.temps);
  }

  /// Whether the value a local has after the step at `index` is only passed
  /// on by the rest of the stage.
  fn local_passed_on(&self, index: usize, local: Local) -> bool {
    let stage = &self.vir.stages[self.stage];
    for (i, step) in stage.steps.iter().enumerate().skip(index + 1) {
      match step {
        Step::Invoke(_, l, invocation) if *l == local => {
          return match invocation {
            Invocation::Read(p) | Invocation::ReadBarrier(p) | Invocation::ReadWrite(p, _) => {
              match p.kind {
                PortKind::Wire(_, w) => self.passed_on((self.stage, w), i, 1),
                _ => false,
              }
            }
            _ => true,
          };
        }
        Step::Transfer(transfer)
          if self.vir.interfaces[transfer.interface].wires.contains_key(&local) =>
        {
          return false;
        }
        _ => {}
      }
    }
    true
  }

  /// Frees the holes holding any of the given registers, discarding their
  /// values once they arrive.
  fn discard_held(&mut self, reg: Reg, len: u32) {
    // Values computed by tasks are simply not used.
    for i in 0..len {
      self.in_task.remove(&reg.offset(i));
    }
    self.align_holes(reg, len);
    // Values which will be written through virtual spaces are held, so that
    // they are freed too.
    for i in 0..len {
      if let Some(&(space, _)) = self.unwritten.get(&reg.offset(i)) {
        self.hold(space);
      }
    }
    for i in 0..len {
      if let Some(&(hole, _)) = self.held.get(&reg.offset(i)) {
        let targets = self.holes.remove(&hole).unwrap();
        for target in &targets {
          self.held.remove(target);
        }
        self.discard_held_hole(hole, targets.len() as u32);
      }
    }
  }

  /// Frees a hole, discarding its value of `len` words once it arrives.
  fn discard_held_hole(&mut self, hole: Reg, len: u32) {
    self.holes.remove(&hole);
    let space = self.null_space();
    self.code.push(Instr::HoleForward { hole, space, len });
  }

  /// Returns a space which discards what is written into it.
  fn null_space(&mut self) -> Reg {
    let space = self.alloc(1);
    self.code.push(Instr::Const { dst: space, value: 0 });
    space
  }

  /// Whether the value of the wire, produced by the step at `from`, is only
  /// passed on (into a local, a frame, or the result), rather than used by
  /// this stage.
  fn passed_on(&self, key: WireKey, from: usize, depth: usize) -> bool {
    if depth > 8 || key.0 != self.stage {
      return false;
    }
    let stage = &self.vir.stages[self.stage];
    let is_wire = |port: &Port| matches!(port.kind, PortKind::Wire(_, w) if w == key.1);
    let wire_of = |port: &Port| match port.kind {
      PortKind::Wire(_, w) => Some((self.stage, w)),
      _ => None,
    };
    if stage.header.ports().any(is_wire) {
      // The result.
      return true;
    }
    let Some((index, step)) =
      stage.steps.iter().enumerate().find(|&(i, step)| i != from && step.ports().any(is_wire))
    else {
      return false;
    };
    let follow = |port: &Port| wire_of(port).is_some_and(|k| self.passed_on(k, index, depth + 1));
    match step {
      Step::Invoke(_, local, invocation) => {
        let written = match invocation {
          Invocation::Write(p) | Invocation::BarrierWrite(p) | Invocation::ReadWrite(_, p) => {
            is_wire(p)
          }
          _ => false,
        };
        // The local's value is passed on if its next read passes it on.
        written
          && stage.steps.iter().enumerate().skip(index + 1).find_map(|(i, step)| match step {
            Step::Invoke(_, l, invocation) if l == local => Some(match invocation {
              Invocation::Read(p) | Invocation::ReadBarrier(p) | Invocation::ReadWrite(p, _) => {
                wire_of(p).is_some_and(|k| self.passed_on(k, i, depth + 1))
              }
              _ => true,
            }),
            _ => None,
          }) != Some(false)
      }
      Step::Composite(port, fields) => fields.iter().any(is_wire) && follow(port),
      Step::Enum(_, _, port, data) => is_wire(data) && follow(port),
      Step::Ref(reference, value, _) => is_wire(value) && follow(reference),
      Step::Rewrap(a, b) | Step::Link(a, b) | Step::Union(_, _, a, b) => {
        if is_wire(a) {
          follow(b)
        } else {
          follow(a)
        }
      }
      Step::Call(_, rel, args, _) => {
        args.iter().any(is_wire)
          && match self.e.specs.spec(self.spec_id).rels.fns[*rel] {
            Ok((callee, _)) => {
              self.e.intrinsic(callee).is_none()
                && matches!(self.e.specs.spec(callee).kind, SpecKind::Fragment(_))
            }
            Err(_) => false,
          }
      }
      _ => false,
    }
  }

  /// Makes a virtual space real, pointing into the continuation frame.
  fn materialize_cont(&mut self, space: Reg) {
    let Some(targets) = self.virtual_spaces.remove(&space) else { return };
    if self.cont.is_none() {
      let frame = self.alloc(1);
      let block =
        self.e.program.blocks.push(Block { unit: self.unit, entry: Label(0), frame: vec![] });
      self.code.push(Instr::NewFrame { dst: frame, block });
      self.cont = Some(Cont { frame, block, map: Vec::new() });
    }
    let cont = self.cont.as_mut().unwrap();
    let offset = 1 + cont.map.len() as u32;
    for target in targets {
      self.unwritten.remove(&target);
      self.pending.insert(target, cont.map.len());
      cont.map.push(target);
    }
    let frame = cont.frame;
    self.code.push(Instr::Space { dst: space, frame, offset });
  }

  fn materialize_range(&mut self, reg: Reg, len: u32) {
    for i in 0..len {
      self.materialize(reg.offset(i));
    }
  }

  /// Writes `len` words into a space.
  fn emit_write(&mut self, space: Reg, src: Reg, len: u32) {
    if let Some(targets) = self.virtual_spaces.remove(&space) {
      for (i, target) in targets.into_iter().enumerate() {
        self.unwritten.remove(&target);
        self.move_regs(target, src.offset(i as u32), 1);
      }
      return;
    }
    if self.remote(space, 1) {
      // The space is not available yet; a task writes the value into it once
      // it is.
      let mut task = self.new_task();
      let space = self.task_input(&mut task, space, 1);
      let src = self.task_input(&mut task, src, len);
      task.code.push(Instr::Write { space, src, len });
      self.finish_task(task);
      return;
    }
    // Parts of the value which will themselves be written through virtual
    // spaces are written directly into the corresponding parts of `space`:
    // the virtual spaces become spaces for those parts.
    self.align_holes(src, len);
    let runs = self.runs(src, len);
    if runs.iter().all(|run| run.2 == Run::Real) {
      self.materialize_range(src, len);
      self.require(src, len);
      self.require(space, 1);
      self.code.push(Instr::Write { space, src, len });
      return;
    }
    for &(start, len, kind) in &runs {
      if kind == Run::Real {
        self.materialize_range(src.offset(start), len);
        self.require(src.offset(start), len);
      }
    }
    self.require(space, 1);
    let parts = if runs.len() == 1 {
      space
    } else {
      let parts = self.alloc(runs.len() as u32);
      let offsets = runs.iter().map(|run| run.0).collect();
      let dsts = (0..runs.len() as u32).map(|i| parts.offset(i)).collect();
      self.code.push(Instr::Split { space, offsets, dsts });
      parts
    };
    for (i, (start, len, kind)) in runs.into_iter().enumerate() {
      let part = parts.offset(i as u32);
      let src = src.offset(start);
      match kind {
        Run::Virtual => {
          let virtual_space = self.take_virtual(src, len);
          self.code.push(Instr::Move { dst: virtual_space, src: part, len: 1 });
        }
        Run::Held => {
          let hole = self.take_held(src, len);
          self.code.push(Instr::HoleForward { hole, space: part, len });
        }
        Run::Task(task) => self.task_write(task, part, src, len),
        Run::Real => self.code.push(Instr::Write { space: part, src, len }),
      }
    }
  }

  /// Removes the virtual space the registers are written through.
  fn take_virtual(&mut self, src: Reg, len: u32) -> Reg {
    let (space, _) = self.unwritten[&src];
    for j in 0..len {
      self.unwritten.remove(&src.offset(j));
    }
    self.virtual_spaces.remove(&space);
    space
  }

  /// Removes the hole the registers are held by.
  fn take_held(&mut self, src: Reg, len: u32) -> Reg {
    let (hole, _) = self.held[&src];
    for j in 0..len {
      self.held.remove(&src.offset(j));
    }
    self.holes.remove(&hole);
    hole
  }

  /// Splits registers into runs, each either written through one virtual
  /// space, held by one hole, or neither; returns their starts, lengths, and
  /// kinds.
  fn runs(&self, src: Reg, len: u32) -> Vec<(u32, u32, Run)> {
    let mut runs = Vec::new();
    let mut i = 0;
    while i < len {
      if let Some(run) = self.special_run(src.offset(i), len - i) {
        runs.push((i, run.0, run.1));
        i += run.0;
        continue;
      }
      let start = i;
      while i < len && self.special_run(src.offset(i), len - i).is_none() {
        i += 1;
      }
      runs.push((start, i - start, Run::Real));
    }
    runs
  }

  fn special_run(&self, reg: Reg, max: u32) -> Option<(u32, Run)> {
    if let Some(len) = self.virtual_run(reg, max) {
      return Some((len, Run::Virtual));
    }
    if let Some(&(task, _)) = self.in_task.get(&reg) {
      let mut len = 1;
      while len < max && self.in_task.get(&reg.offset(len)).map(|x| x.0) == Some(task) {
        len += 1;
      }
      return Some((len, Run::Task(task)));
    }
    let &(hole, 0) = self.held.get(&reg)? else { return None };
    let targets = &self.holes[&hole];
    let len = targets.len() as u32;
    (len <= max && (0..len).all(|i| targets[i as usize] == reg.offset(i)))
      .then_some((len, Run::Held))
  }

  /// Fills `len` words of another frame. Words which will be written through
  /// a virtual space are written into the frame directly: the virtual space
  /// becomes a space pointing into it.
  fn emit_fill(&mut self, frame: Reg, offset: u32, src: Reg, len: u32) {
    self.align_holes(src, len);
    for (start, len, kind) in self.runs(src, len) {
      let (src, offset) = (src.offset(start), offset + start);
      match kind {
        Run::Virtual => {
          let space = self.take_virtual(src, len);
          self.code.push(Instr::Space { dst: space, frame, offset });
        }
        Run::Held => {
          let hole = self.take_held(src, len);
          let space = self.alloc(1);
          self.code.push(Instr::Space { dst: space, frame, offset });
          self.code.push(Instr::HoleForward { hole, space, len });
        }
        Run::Task(task) => {
          let space = self.alloc(1);
          self.code.push(Instr::Space { dst: space, frame, offset });
          self.task_write(task, space, src, len);
        }
        Run::Real => {
          self.materialize_range(src, len);
          self.require(src, len);
          self.code.push(Instr::Fill { frame, offset, src, len });
        }
      }
    }
  }

  /// If `reg` is the first of the registers written through a virtual space,
  /// all within the next `max` registers, returns their number.
  fn virtual_run(&self, reg: Reg, max: u32) -> Option<u32> {
    let &(space, 0) = self.unwritten.get(&reg)? else { return None };
    let targets = &self.virtual_spaces[&space];
    let len = targets.len() as u32;
    (len <= max && (0..len).all(|i| targets[i as usize] == reg.offset(i))).then_some(len)
  }

  /// Like `require`, but allows registers to be written through virtual
  /// spaces, if they are filled into a frame with `emit_fill`.
  fn require_filled(&mut self, reg: Reg, len: u32) {
    self.align_holes(reg, len);
    for (start, len, kind) in self.runs(reg, len) {
      if kind == Run::Real {
        self.require(reg.offset(start), len);
      }
    }
  }

  /// Moves `len` words; pending words are moved by changing which register
  /// they will be loaded into.
  fn move_regs(&mut self, dst: Reg, src: Reg, len: u32) {
    if dst == src {
      return;
    }
    for i in 0..len {
      let (d, s) = (dst.offset(i), src.offset(i));
      if let Some(index) = self.pending.remove(&s) {
        self.cont.as_mut().unwrap().map[index] = d;
        self.pending.insert(d, index);
      } else if let Some((space, index)) = self.unwritten.remove(&s) {
        self.virtual_spaces.get_mut(&space).unwrap()[index] = d;
        self.unwritten.insert(d, (space, index));
      } else if let Some((hole, index)) = self.held.remove(&s) {
        self.holes.get_mut(&hole).unwrap()[index] = d;
        self.held.insert(d, (hole, index));
      } else if let Some(entry) = self.in_task.remove(&s) {
        self.in_task.insert(d, entry);
      } else if let Some(targets) = self.virtual_spaces.remove(&s) {
        for (index, &target) in targets.iter().enumerate() {
          self.unwritten.insert(target, (d, index));
        }
        self.virtual_spaces.insert(d, targets);
      } else {
        self.code.push(Instr::Move { dst: d, src: s, len: 1 });
      }
    }
  }

  /// Ensures that the given registers are not pending, suspending if
  /// necessary.
  fn require(&mut self, reg: Reg, len: u32) {
    self.release(reg, len);
    if (0..len).any(|i| self.unwritten.contains_key(&reg.offset(i))) {
      self.unsupported("a value used before it is computed".into());
    }
    self.resolve(reg, len);
    if (0..len).any(|i| self.pending.contains_key(&reg.offset(i))) {
      self.suspend();
    }
  }

  /// Waits for all pending values: saves the live registers into the
  /// continuation frame, ends the block, and resumes at a new entry point.
  /// The block ends here (or continues in code emitted separately), so open
  /// tasks are finished too.
  fn suspend(&mut self) {
    self.close_tasks();
    let Some(mut cont) = self.cont.take() else { return };
    let mut saved = BTreeMap::new();
    let live = self.live();
    for (reg, _) in self.live_regs(live) {
      if !self.pending.contains_key(&reg) {
        saved.insert(reg.0, ());
      }
    }
    for &r in saved.keys() {
      let offset = 1 + cont.map.len() as u32;
      self.code.push(Instr::Fill { frame: cont.frame, offset, src: Reg(r), len: 1 });
      cont.map.push(Reg(r));
    }
    self.code.push(Instr::End);
    let entry = self.label();
    self.e.program.blocks[cont.block] = Block { unit: self.unit, entry, frame: cont.map };
    self.pending.clear();
  }

  /// The registers holding values which are still used.
  fn live(&mut self) -> Vec<(Reg, u32)> {
    let mut live = self.outer.clone();
    live.extend(self.temps.iter().copied());
    live.extend(self.live_wires());
    live.extend(self.ret_space.map(|r| (r, 1)));
    live.extend(self.at_end.iter().map(|&(_, action)| (action.reg(), 1)));
    let valid = self.locals.iter().filter(|(_, s)| **s == LocalState::Valid).map(|(l, _)| l);
    for local in valid.collect::<Vec<_>>() {
      live.push(self.local_regs(local));
    }
    live
  }

  /// Finishes the open tasks, as the block filling their frames ends; values
  /// they compute which are still used are held by holes.
  fn close_tasks(&mut self) {
    if self.open_tasks.is_empty() {
      return;
    }
    for (reg, len) in self.live() {
      self.release(reg, len);
    }
    self.in_task.clear();
    self.reader_tasks.clear();
    for task in take(&mut self.open_tasks) {
      self.finish_task(task);
    }
  }

  /// Makes values computed by open tasks held by holes, which the tasks write
  /// them into.
  fn release(&mut self, reg: Reg, len: u32) {
    let mut i = 0;
    while i < len {
      let Some((len, Run::Task(task))) = self.special_run(reg.offset(i), len - i) else {
        i += 1;
        continue;
      };
      let src = reg.offset(i);
      let hole = self.alloc(1);
      self.code.push(Instr::HoleNew { dst: hole, len });
      let space = self.alloc(1);
      self.code.push(Instr::Space { dst: space, frame: hole, offset: 1 });
      self.task_write(task, space, src, len);
      self.hold_regs(hole, (0..len).map(|j| src.offset(j)).collect());
      i += len;
    }
  }

  /// Makes an open task write the value it computes for the given registers
  /// into `space`.
  fn task_write(&mut self, task: usize, space: Reg, src: Reg, len: u32) {
    let slot = self.alloc(1);
    let offset = self.open_tasks[task].offset();
    let frame = self.open_tasks[task].frame;
    self.code.push(Instr::Fill { frame, offset, src: space, len: 1 });
    self.open_tasks[task].map.push(slot);
    let src = self.task_regs(task, src, len, true);
    self.open_tasks[task].code.push(Instr::Write { space: slot, src, len });
  }

  /// The registers of an open task which hold the values it computes for the
  /// given registers, which are made consecutive if necessary; with `take`,
  /// the values are no longer the given registers'.
  fn task_regs(&mut self, task: usize, src: Reg, len: u32, take: bool) -> Reg {
    let regs = (0..len).map(|i| self.in_task[&src.offset(i)].1).collect::<Vec<_>>();
    if take {
      for i in 0..len {
        self.in_task.remove(&src.offset(i));
      }
    }
    if regs.iter().enumerate().all(|(i, &r)| r == regs[0].offset(i as u32)) {
      return regs[0];
    }
    let dst = self.alloc(len);
    for (i, r) in regs.into_iter().enumerate() {
      self.open_tasks[task].code.push(Instr::Move { dst: dst.offset(i as u32), src: r, len: 1 });
    }
    dst
  }

  /// The open task computing all values a step reads which are not
  /// available yet, if there is one; the step can be emitted into it.
  fn task_of(&mut self, step: &Step) -> Option<usize> {
    let mut task = None;
    for port in step.ports() {
      let info = self.port_info(port);
      let Some(key) = info.key else { continue };
      if info.writer || info.layout.size == 0 {
        continue;
      }
      let Some(&WireState::Value(reg, len)) = self.wires.get(&key) else { return None };
      for r in (0..len).map(|i| reg.offset(i)) {
        if let Some(&(t, _)) = self.in_task.get(&r) {
          if task.is_some_and(|task| task != t) {
            return None;
          }
          task = Some(t);
        } else if self.remote(r, 1) {
          return None;
        }
      }
    }
    task
  }

  /// The registers whose values must be preserved to preserve the given
  /// registers: registers written through virtual spaces need not be
  /// preserved, and held registers are preserved by preserving their holes.
  fn live_regs(&self, regs: Vec<(Reg, u32)>) -> Vec<(Reg, u32)> {
    let mut live = Vec::new();
    for (reg, len) in regs {
      for i in 0..len {
        let r = reg.offset(i);
        if let Some(&(hole, _)) = self.held.get(&r) {
          live.push((hole, 1));
        } else if !self.unwritten.contains_key(&r) && !self.virtual_spaces.contains_key(&r) {
          live.push((r, 1));
        }
      }
    }
    live.sort();
    live.dedup();
    live
  }

  /// The registers of the current stage's wires whose values have been
  /// produced but not consumed, and spaces still waiting for values.
  fn live_wires(&self) -> Vec<(Reg, u32)> {
    self
      .wires
      .iter()
      .filter(|((stage, _), _)| *stage == self.stage)
      .filter_map(|(_, state)| match *state {
        WireState::Value(reg, len) => Some((reg, len)),
        WireState::ReaderSpace(space) => Some((space, 1)),
        _ => None,
      })
      .collect()
  }

  /// Reports that something is not supported. The code traps if it is
  /// reached, as it may never be (e.g. in the debug mode branch of an
  /// `if const`); `FRAMES_STRICT` makes it an error.
  fn unsupported(&mut self, what: String) {
    if env::var("FRAMES_PANIC").is_ok() {
      panic!("{what} in {} ({:?}, step {})", self.fragment.path, self.stage, self.step);
    }
    let what = if env::var("FRAMES_DEBUG").is_ok() {
      format!("{what} ({:?}, step {})", self.stage, self.step)
    } else {
      what
    };
    if env::var("FRAMES_STRICT").is_ok() {
      self.unsupported_error(what);
    } else {
      let msg =
        format!("not yet supported by the frames backend: {what} in {}", self.fragment.path);
      self.code.push(Instr::Panic { msg });
    }
  }

  fn unsupported_error(&mut self, what: String) {
    let span = self.fragment.tir.span;
    self.e.error(Diag::FramesUnsupported { span, what });
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Run {
  Real,
  Virtual,
  Held,
  /// Computed by the open task with this index.
  Task(usize),
}

/// What happens with a local's final value when the current scope ends.
#[derive(Debug, Clone, Copy)]
enum AtEnd {
  /// It is written into this space.
  Write(Reg),
  /// It is a space, which this hole's value (of the given size) is forwarded
  /// into.
  Forward(Reg, u32),
}

impl AtEnd {
  fn reg(self) -> Reg {
    match self {
      AtEnd::Write(reg) | AtEnd::Forward(reg, _) => reg,
    }
  }
}

#[derive(Debug, Clone, Copy)]
enum EnvWords {
  Value(u32),
  Space,
}

impl EnvWords {
  fn len(self) -> u32 {
    match self {
      EnvWords::Value(len) => len,
      EnvWords::Space => 1,
    }
  }
}

/// Whether a step only moves data; such steps are emitted once their inputs
/// are available.
fn moves_data(step: &Step) -> bool {
  matches!(
    step,
    Step::Composite(..)
      | Step::Ref(..)
      | Step::Rewrap(..)
      | Step::Link(..)
      | Step::Union(..)
      | Step::Enum(..)
  )
}

/// Whether an intrinsic reads the values of its inputs, rather than only
/// passing them on.
fn reads_inputs(intrinsic: Intrinsic) -> bool {
  !matches!(
    intrinsic,
    Intrinsic::HoleNew
      | Intrinsic::Erase
      | Intrinsic::Forget
      | Intrinsic::F64Drop
      | Intrinsic::Transmute
      | Intrinsic::BlackBox
      | Intrinsic::Unreachable
      | Intrinsic::Panic
  )
}

/// Whether a transfer into an interface creates a value (a closure), rather
/// than transferring control.
fn creates_value(kind: &InterfaceKind) -> bool {
  matches!(kind, InterfaceKind::Closure { .. } | InterfaceKind::Inspect(_))
}

enum ListPart {
  Value((Reg, u32)),
  Char(char),
  Word(u32),
  /// The registers of another list.
  List(Reg),
}

enum CallTarget {
  Rel(FnRelId),
  Spec(SpecId, StageId),
}

enum CallArg {
  Port(Port),
  Regs(Reg, u32),
  /// A reference to a value in these registers; the value is written back
  /// into them.
  Ref(Reg, u32),
}

enum CallRet {
  Port(Port),
  Regs(Reg, u32),
}

enum ArgWords {
  Regs(Reg, u32),
  Space(Reg),
  Ref(Reg, u32),
  /// A value that has not been produced yet, which will be written directly
  /// into the frame.
  Forward(Port, u32),
}

/// Offsets the labels an instruction jumps to.
fn relocate(instr: &mut Instr, base: u32) {
  match instr {
    Instr::Jump { target } => target.0 += base,
    Instr::Branch { then, else_, .. } => {
      then.0 += base;
      else_.0 += base;
    }
    Instr::Switch { targets, .. } => targets.iter_mut().for_each(|target| target.0 += base),
    _ => {}
  }
}

fn set_target(instr: &mut Instr, index: usize, label: Label) {
  match instr {
    Instr::Jump { target } => *target = label,
    Instr::Branch { then, else_, .. } => {
      if index == 0 {
        *then = label
      } else {
        *else_ = label
      }
    }
    Instr::Switch { targets, .. } => targets[index] = label,
    _ => unreachable!(),
  }
}
