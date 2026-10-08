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
//! A space is a single word, however large the slot it points to. A space
//! can be split into spaces for parts of its slot (e.g. the fields of a
//! tuple); the frame then waits for one more write for each additional part.
//!
//! There are no return values: a function receives a space as an argument, and
//! "returns" by writing its result into it, which may make the caller's
//! continuation frame ready.
//!
//! A *hole* is a frame whose code is supplied later: its slots receive a
//! value through spaces, like any other frame, but what happens to the value
//! is decided by the hole's reader, which supplies the code afterwards; e.g.
//! forwarding the value into another space. A hole's header counts the code
//! as one more unfilled slot.
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
