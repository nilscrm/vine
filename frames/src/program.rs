use std::fmt;

use vine_util::{idx::IdxVec, new_idx};

use crate::layout::{LayoutId, Layouts};

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
  pub blocks: IdxVec<BlockId, Block>,
  pub layouts: Layouts,
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

#[derive(Debug, Clone)]
pub struct Block {
  pub name: String,
  /// The number of slots in this block's frames; a frame becomes ready once
  /// this many slots have been filled.
  pub slots: u16,
  /// The number of words in this block's frames, not including the header.
  /// When the block is run, these are loaded into registers `0..frame_size`.
  pub frame_size: u32,
  /// The size of this block's register file.
  pub regs: u32,
  pub code: Vec<Instr>,
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
  /// Deeply copies a value.
  Copy {
    dst: Reg,
    src: Reg,
    layout: LayoutId,
  },
  /// Deeply frees a value.
  Erase {
    src: Reg,
    layout: LayoutId,
  },

  /// Allocates a frame for `block`; none of its slots are filled.
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

  /// Allocates an empty hole for a value of `len` words; the resulting word
  /// is used as both the `Promise` and the `Hole`.
  HoleNew {
    dst: Reg,
    len: u32,
  },
  /// Fills a hole.
  HoleSet {
    hole: Reg,
    src: Reg,
    len: u32,
  },
  /// Once the promised value is available, writes it into `space`.
  HoleForward {
    promise: Reg,
    space: Reg,
    len: u32,
  },
  /// Allocates a filled hole, returning its promise.
  PromiseOf {
    dst: Reg,
    src: Reg,
    len: u32,
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
