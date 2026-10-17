use std::{
  collections::HashSet,
  error::Error,
  fmt,
  io::{self, Read, Write},
  time::{Duration, Instant},
};

use vine_util::idx::IdxVec;

use crate::{
  heap::{Addr, Heap},
  ops::{Op, Ops},
  program::{BlockId, Instr, IoOp, OpId, Program, Reg},
};

/// A frame header holds the number of words still to be written (plus one for
/// the code, if it has not been supplied yet) in its high bits, and the code in
/// its low bits.
const COUNTER_SHIFT: u32 = 48;
const CODE_MASK: u64 = (1 << COUNTER_SHIFT) - 1;
/// The code of a frame whose code has not been supplied yet.
const CODE_NONE: u64 = CODE_MASK;
/// The code of a hole whose value is to be forwarded into the space stored
/// after the value; the low bits hold the value's length.
const CODE_FORWARD: u64 = 1 << (COUNTER_SHIFT - 1);
/// The bits of a space holding the offset within the frame.
const SPACE_OFFSET_BITS: u32 = 16;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeError {
  Panic(String),
  InvalidOp(&'static str),
  UnknownOp(&'static str),
  /// The program stopped without halting, with frames still waiting.
  Deadlock {
    waiting: u64,
  },
  /// A hole was read twice.
  HoleMisuse,
  Io(String),
}

impl fmt::Display for RuntimeError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      RuntimeError::Panic(msg) => write!(f, "panic: {msg}"),
      RuntimeError::InvalidOp(op) => write!(f, "invalid operands to `{op}`"),
      RuntimeError::UnknownOp(op) => write!(f, "unknown operation `{op}`"),
      RuntimeError::Deadlock { waiting } => {
        write!(f, "deadlock: the program stopped with {waiting} objects still live")
      }
      RuntimeError::HoleMisuse => write!(f, "hole read more than once"),
      RuntimeError::Io(err) => write!(f, "io error: {err}"),
    }
  }
}

impl Error for RuntimeError {}

#[derive(Debug, Default, Clone)]
pub struct Stats {
  pub blocks_run: u64,
  pub instructions: u64,
  pub frames: u64,
  pub time: Duration,
}

pub struct Host<'a> {
  pub stdin: Box<dyn Read + 'a>,
  pub stdout: Box<dyn Write + 'a>,
}

impl Host<'static> {
  pub fn stdio() -> Self {
    Host { stdin: Box::new(io::stdin()), stdout: Box::new(io::stdout()) }
  }
}

pub struct Runtime<'p, 'h> {
  program: &'p Program,
  ops: IdxVec<OpId, &'p Op>,
  pub heap: Heap,
  pub host: Host<'h>,
  pub stats: Stats,
  regs: Vec<u64>,
  ready: Vec<Addr>,
  halted: bool,
  scratch: Vec<u64>,
  /// Whether to print each block as it is run, and the frames and holes still
  /// waiting if the program deadlocks.
  pub trace: bool,
  /// With `trace`, the frames and holes which have not run yet.
  waiting: HashSet<Addr>,
}

impl<'p, 'h> Runtime<'p, 'h> {
  pub fn new(program: &'p Program, ops: &'p Ops, host: Host<'h>) -> Result<Self, RuntimeError> {
    for block in program.blocks.values() {
      assert!(block.frame_size() < (1 << (64 - COUNTER_SHIFT)) - 1, "frame too large");
    }
    let ops = program
      .ops
      .values()
      .map(|&name| ops.get(name).ok_or(RuntimeError::UnknownOp(name)))
      .collect::<Result<_, _>>()?;
    Ok(Runtime {
      program,
      ops,
      heap: Heap::new(),
      host,
      stats: Stats::default(),
      regs: Vec::new(),
      ready: Vec::new(),
      halted: false,
      scratch: Vec::new(),
      trace: false,
      waiting: HashSet::new(),
    })
  }

  /// Runs the program until there is no more work to do.
  pub fn run(&mut self) -> Result<(), RuntimeError> {
    let start = Instant::now();
    debug_assert_eq!(self.program.blocks[self.program.entry].frame_size(), 0);
    self.new_frame(self.program.entry);
    let result = self.run_ready();
    self.stats.time += start.elapsed();
    self.host.stdout.flush().map_err(|e| RuntimeError::Io(e.to_string()))?;
    result?;
    if !self.halted {
      if self.trace {
        self.print_waiting();
      }
      Err(RuntimeError::Deadlock { waiting: self.heap.live_objects() })?
    }
    Ok(())
  }

  fn run_ready(&mut self) -> Result<(), RuntimeError> {
    while let Some(frame) = self.ready.pop() {
      self.run_frame(frame)?;
    }
    Ok(())
  }

  fn new_frame(&mut self, block_id: BlockId) -> Addr {
    let size = self.program.blocks[block_id].frame_size();
    let frame = self.heap.alloc(size + 1);
    self.heap.set(frame, ((size as u64) << COUNTER_SHIFT) | block_id.0 as u64);
    self.stats.frames += 1;
    if self.trace {
      self.waiting.insert(frame);
    }
    if size == 0 {
      self.ready.push(frame);
    }
    frame
  }

  fn fill(&mut self, frame: Addr, offset: u32, src: Reg, len: u32) {
    let src = &self.regs[src.0 as usize..][..len as usize];
    self.heap.slice_mut(frame.offset(offset), len).copy_from_slice(src);
    self.decrement(frame, len);
  }

  fn fill_words(&mut self, frame: Addr, offset: u32, words: &[u64]) {
    self.heap.slice_mut(frame.offset(offset), words.len() as u32).copy_from_slice(words);
    self.decrement(frame, words.len() as u32);
  }

  /// Records that `len` more words of `frame` have been written (or that its
  /// code has been supplied, with `len` of `1`).
  fn decrement(&mut self, frame: Addr, len: u32) {
    if len == 0 {
      return;
    }
    let header = self.heap.get(frame);
    debug_assert!(header >> COUNTER_SHIFT >= len as u64, "frame overfilled");
    let header = header - ((len as u64) << COUNTER_SHIFT);
    self.heap.set(frame, header);
    if header >> COUNTER_SHIFT == 0 {
      self.ready.push(frame);
    }
  }

  fn run_frame(&mut self, frame: Addr) -> Result<(), RuntimeError> {
    let program = self.program;
    let code = self.heap.get(frame) & CODE_MASK;
    if code & CODE_FORWARD != 0 {
      self.forward(frame, (code & !CODE_FORWARD) as u32);
      return Ok(());
    }
    let block = &program.blocks[BlockId(code as usize)];
    let unit = &program.units[block.unit];
    self.stats.blocks_run += 1;
    if self.trace {
      self.waiting.remove(&frame);
      let words = self.heap.slice(frame.offset(1), block.frame_size());
      eprintln!("run b{} ({} @ {:?}) at {}: {words:?}", code, unit.name, block.entry, frame.0);
    }
    if self.regs.len() < unit.regs as usize {
      self.regs.resize(unit.regs as usize, 0);
    }
    for (i, reg) in block.frame.iter().enumerate() {
      self.regs[reg.0 as usize] = self.heap.get(frame.offset(i as u32 + 1));
    }
    self.heap.free(frame, block.frame_size() + 1);

    let mut pc = block.entry.0 as usize;
    loop {
      self.stats.instructions += 1;
      match &unit.code[pc] {
        Instr::Const { dst, value } => self.regs[dst.0 as usize] = *value,
        Instr::Move { dst, src, len } => {
          let src = src.0 as usize;
          self.regs.copy_within(src..src + *len as usize, dst.0 as usize);
        }
        Instr::Op { op, args, rets } => {
          let op = self.ops[*op];
          let mut inputs = [0; 4];
          for (input, arg) in inputs.iter_mut().zip(args) {
            *input = self.regs[arg.0 as usize];
          }
          self.scratch.clear();
          (op.f)(&inputs[..args.len()], &mut self.scratch)
            .map_err(|_| RuntimeError::InvalidOp(op.name))?;
          for (ret, &word) in rets.iter().zip(&self.scratch) {
            self.regs[ret.0 as usize] = word;
          }
        }
        Instr::Io { op, args, rets } => {
          let args = args.iter().map(|r| self.regs[r.0 as usize]).collect::<Vec<_>>();
          let out = self.io(*op, &args)?;
          for (ret, word) in rets.iter().zip(out) {
            self.regs[ret.0 as usize] = word;
          }
        }

        Instr::Alloc { dst, len } => self.regs[dst.0 as usize] = self.heap.alloc(*len).0,
        Instr::Free { ptr, len } => self.heap.free(self.addr(*ptr), *len),
        Instr::Load { dst, ptr, offset, len } => {
          let words = self.heap.slice(self.addr(*ptr).offset(*offset), *len);
          self.regs[dst.0 as usize..][..*len as usize].copy_from_slice(words);
        }
        Instr::Store { ptr, offset, src, len } => {
          let addr = self.addr(*ptr).offset(*offset);
          let src = &self.regs[src.0 as usize..][..*len as usize];
          self.heap.slice_mut(addr, *len).copy_from_slice(src);
        }

        Instr::NewFrame { dst, block } => self.regs[dst.0 as usize] = self.new_frame(*block).0,
        Instr::Fill { frame, offset, src, len } => {
          self.fill(self.addr(*frame), *offset, *src, *len);
        }
        Instr::Space { dst, frame, offset } => {
          self.regs[dst.0 as usize] = encode_space(self.addr(*frame), *offset);
        }
        Instr::Write { space, src, len } => {
          let (frame, offset) = decode_space(self.regs[space.0 as usize]);
          self.fill(frame, offset, *src, *len);
        }
        Instr::Split { space, offsets, dsts } => {
          let (frame, base) = decode_space(self.regs[space.0 as usize]);
          for (dst, offset) in dsts.iter().zip(offsets) {
            self.regs[dst.0 as usize] = encode_space(frame, base + offset);
          }
        }

        Instr::HoleNew { dst, len } => {
          let hole = self.heap.alloc(hole_size(*len));
          self.heap.set(hole, ((*len as u64 + 1) << COUNTER_SHIFT) | CODE_NONE);
          self.regs[dst.0 as usize] = hole.0;
          if self.trace {
            self.waiting.insert(hole);
          }
        }
        Instr::HoleOf { dst, src, len } => {
          let hole = self.heap.alloc(hole_size(*len));
          self.heap.set(hole, (1 << COUNTER_SHIFT) | CODE_NONE);
          let src = &self.regs[src.0 as usize..][..*len as usize];
          self.heap.slice_mut(hole.offset(1), *len).copy_from_slice(src);
          self.regs[dst.0 as usize] = hole.0;
          if self.trace {
            self.waiting.insert(hole);
          }
        }
        Instr::HoleForward { hole, space, len } => {
          let hole = self.addr(*hole);
          let header = self.heap.get(hole);
          if header & CODE_MASK != CODE_NONE {
            Err(RuntimeError::HoleMisuse)?
          }
          self.heap.set(hole.offset(len + 1), self.regs[space.0 as usize]);
          self.heap.set(hole, (header & !CODE_MASK) | CODE_FORWARD | *len as u64);
          if header >> COUNTER_SHIFT == 1 {
            self.forward(hole, *len);
          } else {
            self.decrement(hole, 1);
          }
        }
        Instr::HoleTake { hole, dst, len, ok } => {
          let hole = self.addr(*hole);
          let header = self.heap.get(hole);
          if header & CODE_MASK != CODE_NONE {
            Err(RuntimeError::HoleMisuse)?
          }
          let filled = header >> COUNTER_SHIFT == 1;
          if filled {
            let words = self.heap.slice(hole.offset(1), *len);
            self.regs[dst.0 as usize..][..*len as usize].copy_from_slice(words);
            self.heap.free(hole, hole_size(*len));
            self.waiting.remove(&hole);
          }
          self.regs[ok.0 as usize] = filled as u64;
        }

        Instr::Jump { target } => {
          pc = target.0 as usize;
          continue;
        }
        Instr::Branch { cond, then, else_ } => {
          pc = if self.regs[cond.0 as usize] != 0 { then.0 } else { else_.0 } as usize;
          continue;
        }
        Instr::Switch { tag, targets } => {
          pc = targets[self.regs[tag.0 as usize] as usize].0 as usize;
          continue;
        }
        Instr::End => return Ok(()),
        Instr::Halt => self.halted = true,
        Instr::Panic { msg } => Err(RuntimeError::Panic(msg.clone()))?,
      }
      pc += 1;
    }
  }

  /// Prints the frames and holes still waiting, with the number of words (or
  /// code) they are missing.
  fn print_waiting(&self) {
    let mut waiting = self.waiting.iter().copied().collect::<Vec<_>>();
    waiting.sort_by_key(|addr| addr.0);
    for addr in waiting {
      let header = self.heap.get(addr);
      let missing = header >> COUNTER_SHIFT;
      let code = header & CODE_MASK;
      if code == CODE_NONE {
        eprintln!("waiting: hole at {}, missing {missing}", addr.0);
      } else if code & CODE_FORWARD != 0 {
        eprintln!("waiting: forwarding hole at {}, missing {missing}", addr.0);
      } else {
        let block = &self.program.blocks[BlockId(code as usize)];
        let unit = &self.program.units[block.unit].name;
        eprintln!("waiting: b{code} ({unit} @ {:?}) at {}, missing {missing}", block.entry, addr.0);
      }
    }
  }

  fn addr(&self, reg: Reg) -> Addr {
    Addr(self.regs[reg.0 as usize])
  }

  /// Forwards the value of a hole whose value slots have all been filled,
  /// and frees the hole.
  fn forward(&mut self, hole: Addr, len: u32) {
    let words = self.heap.slice(hole.offset(1), len).to_vec();
    let space = self.heap.get(hole.offset(len + 1));
    self.heap.free(hole, hole_size(len));
    self.waiting.remove(&hole);
    let (frame, offset) = decode_space(space);
    self.fill_words(frame, offset, &words);
  }

  fn io(&mut self, op: IoOp, args: &[u64]) -> Result<Vec<u64>, RuntimeError> {
    let err = |e: io::Error| RuntimeError::Io(e.to_string());
    let io = args[0];
    Ok(match op {
      IoOp::PrintChar => {
        let char =
          char::try_from(args[1] as u32).map_err(|_| RuntimeError::InvalidOp("print_char"))?;
        write!(self.host.stdout, "{char}").map_err(err)?;
        vec![io]
      }
      IoOp::PrintByte => {
        self.host.stdout.write_all(&[args[1] as u8]).map_err(err)?;
        vec![io]
      }
      IoOp::Flush => {
        self.host.stdout.flush().map_err(err)?;
        vec![io]
      }
      IoOp::ReadByte => {
        let mut buf = [0];
        let count = self.host.stdin.read(&mut buf).map_err(err)?;
        vec![if count == 0 { u32::MAX as u64 } else { buf[0] as u64 }, io]
      }
      IoOp::ReadChar => {
        self.host.stdout.flush().map_err(err)?;
        let char = match read_char(&mut self.host.stdin).map_err(err)? {
          (0, None) => u32::MAX,
          (_, None) => char::REPLACEMENT_CHARACTER as u32,
          (_, Some(c)) => c as u32,
        };
        vec![char as u64, io]
      }
      IoOp::Ready => vec![1, io],
    })
  }
}

fn encode_space(frame: Addr, offset: u32) -> u64 {
  debug_assert!(offset < 1 << SPACE_OFFSET_BITS);
  (frame.0 << SPACE_OFFSET_BITS) | offset as u64
}

fn decode_space(space: u64) -> (Addr, u32) {
  (Addr(space >> SPACE_OFFSET_BITS), (space & ((1 << SPACE_OFFSET_BITS) - 1)) as u32)
}

/// The size of a hole frame for a value of `len` words: the header, the value,
/// and the space to forward it to.
fn hole_size(len: u32) -> u32 {
  len + 2
}

/// Reads a single unicode character, returning the number of bytes read, and
/// the character, if the bytes were valid UTF-8.
fn read_char(reader: &mut impl Read) -> io::Result<(usize, Option<char>)> {
  let mut buf = [0; 4];
  if reader.read(&mut buf[..1])? == 0 {
    return Ok((0, None));
  }
  let len = match buf[0].leading_ones() {
    0 => return Ok((1, Some(buf[0] as char))),
    2 => 2,
    3 => 3,
    4 => 4,
    _ => return Ok((1, None)),
  };
  let count = reader.read(&mut buf[1..len])?;
  if count != len - 1 {
    return Ok((count + 1, None));
  }
  Ok((len, str::from_utf8(&buf[..len]).ok().and_then(|s| s.chars().next())))
}
