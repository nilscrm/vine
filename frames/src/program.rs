use std::{collections::BTreeSet, fmt};

use vine_util::{idx::IdxVec, new_idx};

new_idx!(pub UnitId; n => ["u{n}"]);
new_idx!(pub BlockId; n => ["b{n}"]);
new_idx!(pub OpId; n => ["op{n}"]);

/// A register; an index into the register file of the running block.
///
/// Multi-word values occupy consecutive registers.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Reg(pub u32);

impl Reg {
  pub fn offset(self, offset: u32) -> Reg {
    Reg(self.0 + offset)
  }
}

impl fmt::Debug for Reg {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "r{}", self.0)
  }
}

/// An index of an instruction within a block.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Label(pub u32);

impl fmt::Debug for Label {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, ".{}", self.0)
  }
}

#[derive(Debug, Default, Clone)]
pub struct Program {
  pub units: IdxVec<UnitId, Unit>,
  pub blocks: IdxVec<BlockId, Block>,
  /// The primitive operations used by the program, by name; see
  /// [`Ops`](crate::ops::Ops).
  pub ops: IdxVec<OpId, &'static str>,
  /// The block run at startup, with an empty frame.
  pub entry: BlockId,
}

impl Program {
  /// Returns the id of the primitive operation with the given name, adding it
  /// if necessary.
  pub fn op(&mut self, name: &'static str) -> OpId {
    match self.ops.iter().find(|(_, n)| **n == name) {
      Some((id, _)) => id,
      None => self.ops.push(name),
    }
  }
}

/// A unit of code, with its own register file; typically, everything compiled
/// from one function. Code within a unit jumps between labels; it is entered
/// through [`Block`]s.
#[derive(Debug, Clone)]
pub struct Unit {
  pub name: String,
  /// The size of the unit's register file.
  pub regs: u32,
  pub code: Vec<Instr>,
}

/// An entry point into a unit, run when one of its frames becomes ready.
#[derive(Debug, Clone)]
pub struct Block {
  pub unit: UnitId,
  pub entry: Label,
  /// The registers that the frame's words are loaded into; word `i` (at
  /// offset `i + 1`) is loaded into register `frame[i]`. The frame becomes
  /// ready once all of its words have been written.
  pub frame: Vec<Reg>,
}

impl Block {
  pub fn frame_size(&self) -> u32 {
    self.frame.len() as u32
  }
}

/// A bytecode instruction.
///
/// Offsets into frames include the header word, so the first slot word of a
/// frame is at offset `1`, which is loaded into register `0`.
#[derive(Debug, Clone)]
pub enum Instr {
  /// Sets a register to a constant.
  Const {
    dst: Reg,
    value: u64,
  },
  /// Copies `len` words between registers.
  Move {
    dst: Reg,
    src: Reg,
    len: u32,
  },
  /// Runs a primitive operation, reading one word from each of `args`, and
  /// writing one word to each of `rets`.
  Op {
    op: OpId,
    args: Vec<Reg>,
    rets: Vec<Reg>,
  },
  /// Runs an IO operation, reading one word from each of `args`, and writing
  /// one word to each of `rets`.
  Io {
    op: IoOp,
    args: Vec<Reg>,
    rets: Vec<Reg>,
  },

  /// Allocates a heap object of `len` words.
  Alloc {
    dst: Reg,
    len: u32,
  },
  /// Frees a heap object of `len` words, without freeing its contents.
  Free {
    ptr: Reg,
    len: u32,
  },
  /// Loads `len` words from a heap object.
  Load {
    dst: Reg,
    ptr: Reg,
    offset: u32,
    len: u32,
  },
  /// Stores `len` words into a heap object.
  Store {
    ptr: Reg,
    offset: u32,
    src: Reg,
    len: u32,
  },

  /// Allocates a frame for `block`; none of its words are filled. A frame of
  /// size zero is ready immediately.
  NewFrame {
    dst: Reg,
    block: BlockId,
  },
  /// Fills the slot of `frame` at `offset` with `len` words.
  Fill {
    frame: Reg,
    offset: u32,
    src: Reg,
    len: u32,
  },
  /// Creates a space pointing to the slot of `frame` at `offset`.
  Space {
    dst: Reg,
    frame: Reg,
    offset: u32,
  },
  /// Fills the slot that `space` points to with `len` words.
  Write {
    space: Reg,
    src: Reg,
    len: u32,
  },
  /// Splits `space` into spaces for parts of its slot, at the given offsets
  /// relative to the start of the slot; each of them must then be filled,
  /// instead of the slot as a whole.
  Split {
    space: Reg,
    offsets: Vec<u32>,
    dsts: Vec<Reg>,
  },

  /// Allocates a hole for a value of `len` words: a frame whose code has not
  /// been supplied yet, with the value at offset `1`.
  HoleNew {
    dst: Reg,
    len: u32,
  },
  /// Allocates a hole whose value has already been filled.
  HoleOf {
    dst: Reg,
    src: Reg,
    len: u32,
  },
  /// Supplies a hole's code: once its value has been filled, the value is
  /// written into `space`, and the hole is freed.
  HoleForward {
    hole: Reg,
    space: Reg,
    len: u32,
  },
  /// If a hole's value has been filled, moves it into `dst`, frees the hole,
  /// and sets `ok` to `1`; otherwise, sets `ok` to `0`.
  HoleTake {
    hole: Reg,
    dst: Reg,
    len: u32,
    ok: Reg,
  },

  Jump {
    target: Label,
  },
  /// Jumps to `then` if `cond` is nonzero, and to `else_` otherwise.
  Branch {
    cond: Reg,
    then: Label,
    else_: Label,
  },
  /// Jumps to `targets[tag]`.
  Switch {
    tag: Reg,
    targets: Vec<Label>,
  },
  /// Finishes running the block.
  End,
  /// Marks the program as having finished successfully.
  Halt,
  /// Aborts the program with an error.
  Panic {
    msg: String,
  },
}

/// An operation interacting with the outside world.
///
/// The IO handle is a word that is threaded through the operations, which
/// orders them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IoOp {
  /// `(io, char) -> io`
  PrintChar,
  /// `(io, byte) -> io`
  PrintByte,
  /// `io -> io`
  Flush,
  /// `io -> (char, io)`; the char is `u32::MAX` at the end of the input.
  ReadChar,
  /// `io -> (byte, io)`; the byte is `u32::MAX` at the end of the input.
  ReadByte,
  /// `io -> (bool, io)`
  Ready,
}

impl IoOp {
  pub fn arity(self) -> (usize, usize) {
    match self {
      IoOp::PrintChar | IoOp::PrintByte => (2, 1),
      IoOp::Flush => (1, 1),
      IoOp::ReadChar | IoOp::ReadByte | IoOp::Ready => (1, 2),
    }
  }
}

impl Instr {
  /// The registers the instruction reads, and the registers it writes.
  pub fn regs(&self) -> (Vec<Reg>, Vec<Reg>) {
    let range = |reg: Reg, len: u32| (0..len).map(move |i| reg.offset(i));
    match self {
      Instr::Const { dst, .. } => (vec![], vec![*dst]),
      Instr::Move { dst, src, len } => (range(*src, *len).collect(), range(*dst, *len).collect()),
      Instr::Op { args, rets, .. } | Instr::Io { args, rets, .. } => (args.clone(), rets.clone()),
      Instr::Alloc { dst, .. } => (vec![], vec![*dst]),
      Instr::Free { ptr, .. } => (vec![*ptr], vec![]),
      Instr::Load { dst, ptr, len, .. } => (vec![*ptr], range(*dst, *len).collect()),
      Instr::Store { ptr, src, len, .. } => {
        ([*ptr].into_iter().chain(range(*src, *len)).collect(), vec![])
      }
      Instr::NewFrame { dst, .. } => (vec![], vec![*dst]),
      Instr::Fill { frame, src, len, .. } => {
        ([*frame].into_iter().chain(range(*src, *len)).collect(), vec![])
      }
      Instr::Space { dst, frame, .. } => (vec![*frame], vec![*dst]),
      Instr::Write { space, src, len } => {
        ([*space].into_iter().chain(range(*src, *len)).collect(), vec![])
      }
      Instr::Split { space, dsts, .. } => (vec![*space], dsts.clone()),
      Instr::HoleNew { dst, .. } => (vec![], vec![*dst]),
      Instr::HoleOf { dst, src, len } => (range(*src, *len).collect(), vec![*dst]),
      Instr::HoleForward { hole, space, .. } => (vec![*hole, *space], vec![]),
      Instr::HoleTake { hole, dst, len, ok } => {
        (vec![*hole], range(*dst, *len).chain([*ok]).collect())
      }
      Instr::Branch { cond, .. } => (vec![*cond], vec![]),
      Instr::Switch { tag, .. } => (vec![*tag], vec![]),
      Instr::Jump { .. } | Instr::End | Instr::Halt | Instr::Panic { .. } => (vec![], vec![]),
    }
  }
}

impl Program {
  /// Checks that every block only reads registers which are loaded from its
  /// frame, or written by earlier instructions of the block; returns a
  /// description of each violation.
  pub fn check_registers(&self) -> Vec<String> {
    let mut errors = Vec::new();
    for (block_id, block) in self.blocks.iter() {
      let Some(unit) = self.units.get(block.unit) else { continue };
      // The registers which are certainly written at each label reached.
      let mut written: Vec<Option<BTreeSet<Reg>>> = vec![None; unit.code.len()];
      let mut queue = vec![(block.entry.0 as usize, block.frame.iter().copied().collect())];
      while let Some((pc, regs)) = queue.pop() {
        let Some(instr) = unit.code.get(pc) else { continue };
        let regs: BTreeSet<Reg> = match &written[pc] {
          Some(old) if old.is_subset(&regs) => continue,
          Some(old) => old.intersection(&regs).copied().collect(),
          None => regs,
        };
        written[pc] = Some(regs.clone());
        let (reads, writes) = instr.regs();
        for reg in reads {
          if !regs.contains(&reg) {
            errors.push(format!(
              "{block_id:?} ({}) reads {reg:?} at {pc} ({instr:?}) before it is written",
              unit.name
            ));
          }
        }
        let mut regs = regs;
        regs.extend(writes);
        match instr {
          Instr::Jump { target } => queue.push((target.0 as usize, regs)),
          Instr::Branch { then, else_, .. } => {
            queue.push((then.0 as usize, regs.clone()));
            queue.push((else_.0 as usize, regs));
          }
          Instr::Switch { targets, .. } => {
            queue.extend(targets.iter().map(|target| (target.0 as usize, regs.clone())));
          }
          Instr::End | Instr::Panic { .. } => {}
          _ => queue.push((pc + 1, regs)),
        }
      }
    }
    errors.sort();
    errors.dedup();
    errors
  }
}

impl fmt::Display for Program {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for (id, unit) in self.units.iter() {
      writeln!(f, "{id:?} {} (regs: {})", unit.name, unit.regs)?;
      for (block_id, block) in self.blocks.iter() {
        if block.unit == id {
          writeln!(f, "  {block_id:?} @ {:?} <- {:?}", block.entry, block.frame)?;
        }
      }
      for (i, instr) in unit.code.iter().enumerate() {
        writeln!(f, "  {i:>4}: {instr:?}")?;
      }
    }
    Ok(())
  }
}
