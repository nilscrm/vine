//! A runtime for Vine based on heap-allocated *frames*.
//!
//! A program consists of [`Unit`](program::Unit)s of bytecode, each with its
//! own register file, entered through [`Block`](program::Block)s. Code runs
//! until it reaches [`Instr::End`](program::Instr::End); it never stops
//! partway through.
//!
//! A *frame* is a heap object that waits for values before running a block.
//! It consists of a header word, holding the block to run and the number of
//! words still to be written, followed by the frame's words. Values are written
//! into a frame through a *space*, a word pointing to a slot within it; a space
//! is a single word, however large the slot, and it can be split into spaces
//! for parts of the slot (e.g. the fields of a tuple) without any bookkeeping.
//! Once all of a frame's words have been written, the frame is *ready*; when it
//! is run, its words are loaded into the block's registers, and it is freed.
//!
//! There are no return values: a function receives a space as an argument, and
//! "returns" by writing its result into it, which may make the caller's
//! continuation frame ready.
//!
//! A space into frame `0` discards what is written into it.
//!
//! A frame's code may also be supplied after it is created, by whoever reads
//! it: its words are written through spaces as usual, and the code decides
//! what is done with them, e.g. writing them into another space. Data which is
//! not stored inline (boxes, the environments of closures, ...) is held this
//! way. A frame's header counts its code as one more word still to be written,
//! until it is supplied.
//!
//! Values are stored inline, using as many words as their type's layout
//! requires; the runtime itself does not know about types or layouts.

pub mod heap;
pub mod ops;
pub mod program;
pub mod runtime;
