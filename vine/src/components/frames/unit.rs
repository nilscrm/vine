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
//! writer gets that space; otherwise, the value will arrive in a slot of the
//! current *continuation frame*.
//!
//! # Waiting
//!
//! Registers whose values will arrive in the continuation frame are *pending*.
//! Moving a pending value only changes which register the slot is loaded into;
//! only code which reads the value waits, by *suspending*: the live registers
//! are saved into the continuation frame, the block ends, and execution resumes
//! at a new entry point once the frame is ready.
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
  mem::take,
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
  at_end: Vec<(Local, Reg)>,
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
    temps: Vec::new(),
    ret_space: None,
    result: None,
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
  /// Registers read by the current step, which must be preserved if it
  /// suspends.
  temps: Vec<(Reg, u32)>,

  ret_space: Option<Reg>,
  /// The header's result, written when the fragment returns.
  result: Option<(WireKey, Port)>,
  /// Spaces to write locals' final values into when the current scope ends.
  at_end: Vec<(Local, Reg)>,

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
    let context = Context {
      outer: Vec::new(),
      locals: IdxVec::from_iter(self.vir.locals.keys().map(|_| LocalState::Empty)),
      at_end: Vec::new(),
    };
    self.queue.push((StageId(0), context));
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
  }

  /// Determines where each stage returns to, which must be unique.
  fn compute_returns(&mut self) -> bool {
    let mut queue = vec![(StageId(0), ReturnPoint::Fragment)];
    while let Some((stage_id, point)) = queue.pop() {
      if let Some(&existing) = self.returns.get(&stage_id) {
        if existing != point {
          self.unsupported("a stage with several return points".into());
          return false;
        }
        continue;
      }
      self.returns.insert(stage_id, point);
      let steps = &self.vir.stages[stage_id].steps;
      for (index, step) in steps.iter().enumerate() {
        if let Step::Transfer(transfer) = step {
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
    debug_assert!(self.cont.is_none() && self.pending.is_empty());

    let interface = &self.vir.interfaces[stage.interface];
    for (&local, &(input, _, _)) in &interface.wires {
      self.locals[local] = if input { LocalState::Valid } else { LocalState::Empty };
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
      if !self.ready(step) {
        deferred.push((index, step));
        continue;
      }
      self.emit_step(index, step);
      self.emit_deferred(&mut deferred);
    }
    self.emit_deferred(&mut deferred);
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
        self.header_result(result, &mut map);
        self.entries.push((stage_id, label, map));
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

  fn header_result(&mut self, result: &Port, map: &mut Vec<Reg>) {
    let info = self.port_info(result);
    if info.layout.size != 0 {
      let space = self.alloc(1);
      map.push(space);
      self.ret_space = Some(space);
    }
    if let Some(key) = info.key {
      self.result = Some((key, result.clone()));
    }
  }

  fn end_stage(&mut self) {
    let stage = &self.vir.stages[self.stage];
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
        let interface = &self.vir.interfaces[stage.interface];
        for local in self.locals.keys().collect::<Vec<_>>() {
          match interface.wires.get(&local) {
            Some(&(_, _, true)) => _ = self.local_value(local),
            Some(_) => self.drop_local(local),
            None => {}
          }
        }
        self.suspend();
        self.fixups.push((self.code.len(), 0, Fixup::Return(point)));
        self.code.push(Instr::Jump { target: Label(0) });
      }
    }
    self.stage_ended = true;
  }

  fn emit_deferred(&mut self, deferred: &mut Vec<(usize, &Step)>) {
    while let Some(i) = deferred.iter().position(|(_, step)| self.ready(step)) {
      let (index, step) = deferred.remove(i);
      self.step = index;
      self.emit_step(index, step);
    }
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
      Step::Ref(reference, value, _) => {
        if self.port_info(reference).writer {
          if self.port_info(value).writer { vec![] } else { vec![value] }
        } else {
          vec![reference]
        }
      }
      Step::Rewrap(a, b) | Step::Link(a, b) | Step::Union(_, _, a, b) => {
        if self.port_info(a).writer { vec![b] } else { vec![a] }
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
    // Each entry stays in `at_end` until it has been written, so that its
    // space is preserved if writing it waits for the value.
    while let Some(&(local, space)) = self.at_end.first() {
      if let Some(local) = self.final_local(local) {
        let (reg, len) = self.local_value(local);
        self.require(reg, len);
        self.locals[local] = LocalState::Empty;
        self.write_back(space, (reg, len));
      }
      self.at_end.remove(0);
    }
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
      Step::Ref(reference, value, space) => {
        self.emit_composite(reference, &[value.clone(), space.clone()])
      }
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
      if let Some(key) = info.key {
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
        if let Some(rel) = self.vir.locals[local].drop {
          self.call_rel(Span::NONE, rel, vec![CallArg::Regs(reg, len)], None);
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
          if index + 1 == stage.steps.len() {
            // A final transfer; the stage ends here.
            return false;
          }
        }
        _ => {}
      }
    }
    let interface = &self.vir.interfaces[stage.interface];
    matches!(interface.wires.get(&local), Some(&(_, _, true)))
  }

  // Control flow

  fn emit_transfer(&mut self, index: usize, transfer: &Transfer) {
    let interface = &self.vir.interfaces[transfer.interface];
    let stage = &self.vir.stages[self.stage];
    let child = index + 1 != stage.steps.len();

    let data = transfer.data.as_ref().map(|data| self.read_value(data));

    // Pass the locals the target needs; they are kept in their registers.
    for (&local, &(input, _, _)) in &interface.wires {
      if input {
        self.local_value(local);
      }
    }
    if !child {
      // The stage ends here; drop any other locals.
      for local in self.locals.keys().collect::<Vec<_>>() {
        if !matches!(interface.wires.get(&local), Some(&(true, _, _))) {
          self.drop_local(local);
        }
      }
    }
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
    if let Some((reg, len)) = data {
      self.require(reg, len);
    }
    self.suspend();

    let target_context = if child {
      let mut outer = self.outer.clone();
      outer.extend(self.live_wires());
      outer.extend(self.ret_space.map(|r| (r, 1)));
      outer.extend(self.at_end.iter().map(|&(_, space)| (space, 1)));
      let mut locals = self.locals.clone();
      for (&local, &(input, _, _)) in &interface.wires {
        if input {
          locals[local] = LocalState::Empty;
        }
      }
      let valid = self.locals.iter().filter(|&(local, &state)| {
        state == LocalState::Valid && !matches!(interface.wires.get(&local), Some(&(true, _, _)))
      });
      for local in valid.map(|(l, _)| l).collect::<Vec<_>>() {
        outer.push(self.local_regs(local));
      }
      outer.extend(kept.iter().map(|&(_, copy, len)| (copy, len)));
      Context { outer, locals, at_end: Vec::new() }
    } else {
      Context {
        outer: self.outer.clone(),
        locals: self.locals.clone(),
        at_end: self.at_end.clone(),
      }
    };
    for target in interface.kind.stages() {
      self.queue.push((target, target_context.clone()));
    }

    match &interface.kind {
      InterfaceKind::Unconditional(target) => self.jump(*target),
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
      self.return_labels.insert(ReturnPoint::After(self.stage, index), self.label());
      for (&local, &(input, _, output)) in &interface.wires {
        if output {
          self.locals[local] = LocalState::Valid;
        } else if input {
          self.locals[local] = LocalState::Empty;
        }
      }
      for (local, copy, len) in kept {
        let (reg, _) = self.local_regs(local);
        self.move_regs(reg, copy, len);
        self.locals[local] = LocalState::Valid;
      }
    } else {
      self.stage_ended = true;
    }
  }

  fn jump(&mut self, stage: StageId) {
    self.fixups.push((self.code.len(), 0, Fixup::Stage(stage)));
    self.code.push(Instr::Jump { target: Label(0) });
  }

  // Calls

  fn emit_call(&mut self, span: Span, rel: FnRelId, args: &[Port], ret: &Port) {
    let Ok((callee, _)) = self.e.specs.spec(self.spec_id).rels.fns[rel] else { return };
    if let Some(intrinsic) = self.e.intrinsic(callee) {
      return self.emit_intrinsic(span, intrinsic, args, ret);
    }
    if let SpecKind::Synthetic(item) = &self.e.specs.spec(callee).kind {
      let item = item.clone();
      return self.emit_synthetic(&item, args, ret);
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
        let [CallArg::Ref(reg, len)] = &args[..] else { unreachable!() };
        let (copy, _) = ret.unwrap();
        self.require(*reg, *len);
        self.code.push(Instr::Move { dst: copy, src: *reg, len: *len });
      }
      Some(Intrinsic::Erase | Intrinsic::Forget) => {}
      _ => self.call(span, CallTarget::Rel(rel), args, ret.map(|(r, l)| CallRet::Regs(r, l))),
    }
  }

  fn call(&mut self, _span: Span, target: CallTarget, args: Vec<CallArg>, ret: Option<CallRet>) {
    let (callee, stage) = match target {
      CallTarget::Rel(rel) => match self.e.specs.spec(self.spec_id).rels.fns[rel] {
        Ok(x) => x,
        Err(_) => return,
      },
      CallTarget::Const(spec) => (spec, StageId(0)),
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
            self.require(reg, len);
            ArgWords::Regs(reg, len)
          }
        }
        CallArg::Regs(reg, len) => {
          self.require(*reg, *len);
          ArgWords::Regs(*reg, *len)
        }
        CallArg::Ref(reg, len) => {
          self.require(*reg, *len);
          ArgWords::Ref(*reg, *len)
        }
      });
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
    if let SpecKind::Synthetic(item) = &self.e.specs.spec(callee).kind {
      let item = item.clone();
      return self.emit_synthetic(&item, &[], port);
    }
    let info = self.port_info(port);
    let ret = (info.layout.size != 0).then(|| CallRet::Port(port.clone()));
    self.call(span, CallTarget::Const(callee), vec![], ret);
  }

  fn emit_synthetic(&mut self, item: &SyntheticItem, args: &[Port], ret: &Port) {
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
      SyntheticItem::Identity
      | SyntheticItem::CompositeDeconstruct(_)
      | SyntheticItem::CompositeReconstruct(_) => {
        // These only reinterpret a value's words.
        let (reg, len) = self.read_value(&args[0]);
        self.write_value(ret, reg, len);
      }
      item => self.unsupported(format!("{item:?}")),
    }
  }

  fn emit_intrinsic(&mut self, span: Span, intrinsic: Intrinsic, args: &[Port], ret: &Port) {
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
          self.e.error(Diag::TransmuteSize { span, from: len, to: size });
          return;
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
        let len = self.port_info(ret).layout.size;
        let space = self.wire_space(ret);
        self.materialize(space);
        self.code.push(Instr::HoleForward { hole, space, len });
      }
      HoleForward => {
        let (hole, _) = self.read_value(&args[0]);
        self.require(hole, 1);
        let len = self.port_info(&args[1]).layout.size;
        let space = self.wire_space(&args[1]);
        self.materialize(space);
        self.code.push(Instr::HoleForward { hole, space, len });
      }
      HoleAsRef => self.unsupported("Hole::as_ref".into()),
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
    let node_size = element_size + 1;
    let list = self.alloc(3);
    let mut count = 0;
    let mut lists = Vec::new();
    self.code.push(Instr::HoleNew { dst: list.offset(1), len: node_size });
    let mut tail = self.alloc(1);
    self.code.push(Instr::Space { dst: tail, frame: list.offset(1), offset: 1 });
    for part in parts {
      match part {
        ListPart::Value(_) | ListPart::Char(_) => {
          let node = self.alloc(node_size);
          match part {
            ListPart::Value((reg, len)) => self.move_regs(node, reg, len),
            ListPart::Char(c) => self.code.push(Instr::Const { dst: node, value: c as u64 }),
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
          self.require(other, 3);
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

  fn emit_link(&mut self, a: &Port, b: &Port) {
    let (writer, reader) = if self.port_info(a).writer { (a, b) } else { (b, a) };
    let info = self.port_info(writer);
    if info.layout.size == 0 {
      return;
    }
    let reader_info = self.port_info(reader);
    if let Some(key) = reader_info.key
      && let Some(WireState::LocalAtEnd(local)) = self.wires.get(&key).copied()
    {
      self.wires.insert(key, WireState::Consumed);
      let writer_key = info.key.unwrap();
      let state = match self.wires.get(&writer_key).copied() {
        Some(WireState::ReaderSpace(space)) => {
          self.at_end.push((local, space));
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
    if let Some(key) = reader_info.key
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
    self.write_value(writer, reg, len);
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
      let words: Vec<u64> = match &port.kind {
        PortKind::Nil | PortKind::Error(_) => vec![0; size as usize],
        PortKind::Bool(b) => vec![*b as u64],
        PortKind::N32(n) => vec![*n as u64],
        PortKind::F32(f) => vec![f.to_bits() as u64],
        PortKind::F64(f) => vec![f.to_bits()],
        PortKind::Nat(_) => {
          self.unsupported("`Nat` literals".into());
          vec![0; size as usize]
        }
        PortKind::Wire(..) => unreachable!(),
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
        let (reg, len) = self.local_value(local);
        self.locals[local] = LocalState::Empty;
        self.temps.push((reg, len));
        (reg, len)
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
      _ => _ = self.read_value(port),
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
        self.at_end.push((local, space));
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
      }
      Some(state) => unreachable!("{state:?}"),
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
        let block = self.e.discard_block(len);
        let frame = self.alloc(1);
        self.code.push(Instr::NewFrame { dst: frame, block });
        let space = self.alloc(1);
        self.code.push(Instr::Space { dst: space, frame, offset: 1 });
        space
      }
      Some(state) => unreachable!("{} {key:?} {state:?}", self.fragment.path),
    }
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

  /// Makes a virtual space real, as it escapes the unit: its value will arrive
  /// in the continuation frame.
  fn materialize(&mut self, space: Reg) {
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
    // If the value will itself be written through a virtual space, that space
    // simply becomes `space`.
    if len != 0
      && let Some(&(virtual_space, 0)) = self.unwritten.get(&src)
      && self.virtual_spaces[&virtual_space].len() == len as usize
      && (0..len).all(|i| self.unwritten.get(&src.offset(i)) == Some(&(virtual_space, i as usize)))
    {
      for i in 0..len {
        self.unwritten.remove(&src.offset(i));
      }
      self.virtual_spaces.remove(&virtual_space);
      self.code.push(Instr::Move { dst: virtual_space, src: space, len: 1 });
      return;
    }
    self.materialize_range(src, len);
    self.require(src, len);
    self.require(space, 1);
    self.code.push(Instr::Write { space, src, len });
  }

  /// Fills `len` words of another frame.
  fn emit_fill(&mut self, frame: Reg, offset: u32, src: Reg, len: u32) {
    self.materialize_range(src, len);
    self.require(src, len);
    self.code.push(Instr::Fill { frame, offset, src, len });
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
    if (0..len).any(|i| self.unwritten.contains_key(&reg.offset(i))) {
      self.unsupported("a value used before it is computed".into());
    }
    if (0..len).any(|i| self.pending.contains_key(&reg.offset(i))) {
      self.suspend();
    }
  }

  /// Waits for all pending values: saves the live registers into the
  /// continuation frame, ends the block, and resumes at a new entry point.
  fn suspend(&mut self) {
    let Some(mut cont) = self.cont.take() else { return };
    let mut saved = BTreeMap::new();
    let mut live = self.outer.clone();
    live.extend(self.temps.iter().copied());
    live.extend(self.live_wires());
    live.extend(self.ret_space.map(|r| (r, 1)));
    live.extend(self.at_end.iter().map(|&(_, space)| (space, 1)));
    let valid = self.locals.iter().filter(|(_, s)| **s == LocalState::Valid).map(|(l, _)| l);
    for local in valid.collect::<Vec<_>>() {
      live.push(self.local_regs(local));
    }
    for (reg, len) in live {
      for i in 0..len {
        let r = reg.offset(i);
        if !self.pending.contains_key(&r)
          && !self.unwritten.contains_key(&r)
          && !self.virtual_spaces.contains_key(&r)
        {
          saved.insert(r.0, ());
        }
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

  fn unsupported(&mut self, what: String) {
    if env::var("FRAMES_PANIC").is_ok() {
      panic!("{what} in {} ({:?}, step {})", self.fragment.path, self.stage, self.step);
    }
    let span = self.fragment.tir.span;
    let what = if env::var("FRAMES_DEBUG").is_ok() {
      format!("{what} ({:?}, step {})", self.stage, self.step)
    } else {
      what
    };
    self.e.error(Diag::FramesUnsupported { span, what });
  }
}

enum ListPart {
  Value((Reg, u32)),
  Char(char),
  /// The registers of another list.
  List(Reg),
}

enum CallTarget {
  Rel(FnRelId),
  Const(SpecId),
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
