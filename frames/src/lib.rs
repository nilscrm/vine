//! A runtime for Vine based on heap-allocated *frames*.
//!
//! A program is a collection of [`Block`](program::Block)s of bytecode. Code
//! runs in a block until it reaches [`Instr::End`](program::Instr::End); a
//! block never stops partway through. Each block has a register file of words.
//!
//! A *frame* is a heap object that waits for values before running a block.
//! It consists of a header word, holding the number of slots that are still
//! unfilled and the block to run, followed by the slots' words. Values are put
//! into a slot through a *space*, a word pointing to that slot. Once every slot
//! of a frame has been filled, the frame is *ready*; when it is run, its words
//! are copied into the start of the block's register file, and the frame is
//! freed.
//!
//! There are no return values: a function receives a space as an argument, and
//! "returns" by writing its result into it, which may make the caller's
//! continuation frame ready.
//!
//! A *hole* is a single-use cell for a value that may not exist yet, with one
//! writer (the `Hole`) and one reader (the `Promise`). Unlike a frame, a hole
//! does not know what will happen to its value; the reader decides, by
//! forwarding the value into a space once it is available.
//!
//! Values are stored inline, using as many words as their layout requires.
//! Deep copies and frees of heap data are described by [`Layout`]s.
//!
//! [`Layout`]: layout::Layout

pub mod heap;
pub mod layout;
pub mod ops;
pub mod program;
pub mod runtime;
