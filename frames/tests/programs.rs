use frames::{
  layout::{Field, Layout},
  ops::Ops,
  program::{Block, BlockId, Instr, Instr::*, IoOp, Label, Program, Reg},
  runtime::{Host, Runtime, RuntimeError},
};

fn block(name: &str, slots: u16, frame_size: u32, regs: u32, code: Vec<Instr>) -> Block {
  Block { name: name.into(), slots, frame_size, regs, code }
}

fn r(n: u32) -> Reg {
  Reg(n)
}

fn print(io: Reg, char: Reg) -> Instr {
  Io { op: IoOp::PrintByte, args: vec![io, char], rets: vec![io] }
}

/// Runs a program, returning its output, and the number of heap objects left
/// at the end.
fn run(program: &Program) -> Result<(String, u64), RuntimeError> {
  let ops = Ops::new();
  let mut out = Vec::new();
  let host = Host { stdin: Box::new(&[][..]), stdout: Box::new(&mut out) };
  let mut runtime = Runtime::new(program, &ops, host)?;
  let result = runtime.run();
  let live = runtime.heap.live_objects();
  drop(runtime);
  result?;
  Ok((String::from_utf8(out).unwrap(), live))
}

#[test]
fn hello() {
  let mut program = Program::default();
  program.entry = program.blocks.push(block(
    "entry",
    0,
    0,
    2,
    vec![
      Const { dst: r(0), value: 0 },
      Const { dst: r(1), value: b'h' as u64 },
      print(r(0), r(1)),
      Const { dst: r(1), value: b'i' as u64 },
      print(r(0), r(1)),
      Halt,
      End,
    ],
  ));
  assert_eq!(run(&program), Ok(("hi".into(), 0)));
}

/// `fact(n, ret)`: writes `n!` (mod 2^32) to the space `ret`, recursing
/// through a continuation frame.
fn factorial_program(n: u64) -> Program {
  let mut program = Program::default();
  let mul = program.op("n32:mul");
  let sub = program.op("n32:sub");
  let eq = program.op("n32:eq");
  let entry = BlockId(0);
  let fact = BlockId(1);
  let cont = BlockId(2);
  let done = BlockId(3);
  program.entry = entry;

  // entry: fact(n, space(done))
  _ = program.blocks.push(block(
    "entry",
    0,
    0,
    4,
    vec![
      NewFrame { dst: r(0), block: done },
      Space { dst: r(1), frame: r(0), offset: 1 },
      NewFrame { dst: r(2), block: fact },
      Const { dst: r(3), value: n },
      Fill { frame: r(2), offset: 1, src: r(3), len: 1 },
      Fill { frame: r(2), offset: 2, src: r(1), len: 1 },
      End,
    ],
  ));

  // fact: r0 = n, r1 = ret
  _ = program.blocks.push(block(
    "fact",
    2,
    2,
    8,
    vec![
      Const { dst: r(2), value: 0 },
      Op { op: eq, args: vec![r(0), r(2)], rets: vec![r(3)] },
      Branch { cond: r(3), then: Label(3), else_: Label(6) },
      // 3: n == 0
      Const { dst: r(4), value: 1 },
      Write { space: r(1), src: r(4), len: 1 },
      End,
      // 6: n != 0; cont(n, ret, fact(n - 1, space(cont)))
      NewFrame { dst: r(4), block: cont },
      Fill { frame: r(4), offset: 1, src: r(0), len: 1 },
      Fill { frame: r(4), offset: 2, src: r(1), len: 1 },
      Space { dst: r(5), frame: r(4), offset: 3 },
      NewFrame { dst: r(6), block: fact },
      Const { dst: r(7), value: 1 },
      Op { op: sub, args: vec![r(0), r(7)], rets: vec![r(7)] },
      Fill { frame: r(6), offset: 1, src: r(7), len: 1 },
      Fill { frame: r(6), offset: 2, src: r(5), len: 1 },
      End,
    ],
  ));

  // cont: r0 = n, r1 = ret, r2 = fact(n - 1)
  _ = program.blocks.push(block(
    "cont",
    3,
    3,
    4,
    vec![
      Op { op: mul, args: vec![r(0), r(2)], rets: vec![r(3)] },
      Write { space: r(1), src: r(3), len: 1 },
      End,
    ],
  ));

  // done: r0 = result; prints its low byte
  _ = program.blocks.push(block(
    "done",
    1,
    1,
    2,
    vec![Const { dst: r(1), value: 0 }, print(r(1), r(0)), Halt, End],
  ));

  program
}

#[test]
fn factorial() {
  // 5! = 120 = 'x'
  assert_eq!(run(&factorial_program(5)), Ok(("x".into(), 0)));
}

#[test]
fn deep_recursion() {
  // Recursion goes through heap frames, not the native stack.
  let (out, live) = run(&factorial_program(1_000_000)).unwrap();
  assert_eq!(out.len(), 1);
  assert_eq!(live, 0);
}

/// Creates a hole for a two-word value, whose space is split in two, and
/// filled in two parts; the hole's value is forwarded into a frame, before,
/// between, or after the parts are filled.
fn hole_program(forward_after: usize) -> Program {
  let mut program = Program::default();
  let done = BlockId(1);
  let fill = |part: u32, char: u8| {
    vec![Const { dst: r(3), value: char as u64 }, Write { space: r(5 + part), src: r(3), len: 1 }]
  };
  let forward = vec![
    NewFrame { dst: r(1), block: done },
    Space { dst: r(2), frame: r(1), offset: 1 },
    HoleForward { hole: r(0), space: r(2), len: 2 },
  ];
  let mut parts = vec![fill(0, b'h'), fill(1, b'i')];
  parts.insert(forward_after, forward);
  let mut code = vec![
    HoleNew { dst: r(0), len: 2 },
    Space { dst: r(4), frame: r(0), offset: 1 },
    Split { space: r(4), offsets: vec![0, 1], dsts: vec![r(5), r(6)] },
  ];
  code.extend(parts.into_iter().flatten());
  code.push(End);
  program.entry = program.blocks.push(block("entry", 0, 0, 7, code));
  _ = program.blocks.push(block(
    "done",
    1,
    2,
    3,
    vec![Const { dst: r(2), value: 0 }, print(r(2), r(0)), print(r(2), r(1)), Halt, End],
  ));
  program
}

#[test]
fn holes() {
  for forward_after in 0..3 {
    assert_eq!(run(&hole_program(forward_after)), Ok(("hi".into(), 0)));
  }
}

#[test]
fn hole_take() {
  // `HoleTake` fails while the value is missing, and succeeds once it is
  // filled, or for a hole created with `HoleOf`.
  let mut program = Program::default();
  let code = vec![
    HoleNew { dst: r(0), len: 1 },
    HoleTake { hole: r(0), dst: r(1), len: 1, ok: r(2) },
    Const { dst: r(9), value: 0 },
    Const { dst: r(3), value: b'0' as u64 },
    Op { op: program.op("n32:add"), args: vec![r(2), r(3)], rets: vec![r(4)] },
    print(r(9), r(4)),
    Space { dst: r(5), frame: r(0), offset: 1 },
    Const { dst: r(6), value: b'a' as u64 },
    Write { space: r(5), src: r(6), len: 1 },
    HoleTake { hole: r(0), dst: r(1), len: 1, ok: r(2) },
    print(r(9), r(1)),
    Const { dst: r(6), value: b'b' as u64 },
    HoleOf { dst: r(0), src: r(6), len: 1 },
    HoleTake { hole: r(0), dst: r(1), len: 1, ok: r(2) },
    print(r(9), r(1)),
    Halt,
    End,
  ];
  program.entry = program.blocks.push(block("entry", 0, 0, 10, code));
  assert_eq!(run(&program), Ok(("0ab".into(), 0)));
}

#[test]
fn copy_and_free() {
  // enum List { Nil, Cons(N32, List) }, boxed:
  //   List = 1 word, a pointer to [tag, head, tail]
  let mut program = Program::default();
  let node = program.layouts.reserve();
  let nil = program.layouts.add(Layout::EMPTY);
  let cons =
    program.layouts.add(Layout { size: 2, fields: vec![Field::Box { offset: 1, layout: node }] });
  program.layouts.define(
    node,
    Layout { size: 3, fields: vec![Field::Enum { offset: 0, variants: vec![nil, cons] }] },
  );
  let list =
    program.layouts.add(Layout { size: 1, fields: vec![Field::Box { offset: 0, layout: node }] });

  // Builds [1, 2] in r0, copies it to r1, and frees both.
  let mut code = vec![
    Alloc { dst: r(0), len: 3 },
    Const { dst: r(9), value: 0 },
    Store { ptr: r(0), offset: 0, src: r(9), len: 1 },
  ];
  for value in [2, 1] {
    code.extend([
      Alloc { dst: r(2), len: 3 },
      Const { dst: r(9), value: 1 },
      Store { ptr: r(2), offset: 0, src: r(9), len: 1 },
      Const { dst: r(9), value },
      Store { ptr: r(2), offset: 1, src: r(9), len: 1 },
      Store { ptr: r(2), offset: 2, src: r(0), len: 1 },
      Move { dst: r(0), src: r(2), len: 1 },
    ]);
  }
  code.extend([
    Copy { dst: r(1), src: r(0), layout: list },
    // Free the original; the copy must be intact.
    Erase { src: r(0), layout: list },
    // Print the copy's second element: r1 -> [1, 1, p]; p -> [1, 2, _]
    Load { dst: r(3), ptr: r(1), offset: 2, len: 1 },
    Load { dst: r(4), ptr: r(3), offset: 1, len: 1 },
    Const { dst: r(5), value: b'0' as u64 },
    Op { op: program.op("n32:add"), args: vec![r(4), r(5)], rets: vec![r(4)] },
    Const { dst: r(5), value: 0 },
    print(r(5), r(4)),
    Erase { src: r(1), layout: list },
    Halt,
    End,
  ]);
  program.entry = program.blocks.push(block("entry", 0, 0, 10, code));
  assert_eq!(run(&program), Ok(("2".into(), 0)));
}

#[test]
fn deadlock() {
  let mut program = Program::default();
  let waiting = BlockId(1);
  program.entry =
    program.blocks.push(block("entry", 0, 0, 1, vec![NewFrame { dst: r(0), block: waiting }, End]));
  _ = program.blocks.push(block("waiting", 1, 1, 1, vec![Halt, End]));
  assert_eq!(run(&program), Err(RuntimeError::Deadlock { waiting: 1 }));
}

#[test]
fn errors() {
  let mut program = Program::default();
  let div = program.op("n32:div");
  program.entry = program.blocks.push(block(
    "entry",
    0,
    0,
    2,
    vec![
      Const { dst: r(0), value: 1 },
      Const { dst: r(1), value: 0 },
      Op { op: div, args: vec![r(0), r(1)], rets: vec![r(0)] },
      End,
    ],
  ));
  assert_eq!(run(&program), Err(RuntimeError::InvalidOp("n32:div")));

  let mut program = Program::default();
  program.entry = program.blocks.push(block("entry", 0, 0, 0, vec![Panic { msg: "oh no".into() }]));
  assert_eq!(run(&program), Err(RuntimeError::Panic("oh no".into())));
}
