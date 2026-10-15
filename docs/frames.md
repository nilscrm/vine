# The frames runtime

This branch replaces IVM (interaction nets) with a new runtime built on
*frames*, because interaction nets are suspected to have too much overhead. This
document records the design decisions, how the implementation works, and where
it stands, so that work can be picked up from here. Keep it up to date: when a
decision is made or something lands, change this file in the same commit.

## Status at a glance

- `vine run --frames` compiles a program to frames bytecode and runs it.
- `tests/frames.sh` runs `tests/programs` and `vine/examples` on frames and
  compares their output with the IVM snapshots. See [Status](#status) for the
  latest numbers.
- IVM still works (`vine run`, `vine build`), but compatibility with it is no
  longer a goal (see below).

## Decisions

These were decided together with Nils; don't revisit them without asking.

- **No IVM compatibility.** Make the best choices for frames. The standard
  library is rewritten idiomatically for frames; breaking IVM is fine. (`main`
  keeps IVM; the Ivy backend and the `ivy`/`ivm` crates are to be removed
  eventually.)
- **Lower from VIR + SpecRels**, with a new emitter next to the Ivy one; not
  from Ivy nets.
- **Bytecode interpreter first**; a native backend may come later, with the same
  frame layout.
- **Single-threaded, but atomic-ready**: the frame header's counter is in the
  high 16 bits, so it can be decremented with a `fetch_sub` later.
- **`#[intrinsic = "name"]`** replaces `$ivy` blocks for primitives. Intrinsic
  functions are inlined by the emitter; their bodies are only used by IVM.
- **No erased values.** `Cast[!, T]` traps; `erase` is a deep free and never
  meets a space; there are no null spaces. `eraser` and `move` were removed.
- **No `#[become]`.** `duplicate`/`erase` are only allowed on plain data
  (checked when computing layouts); otherwise `Fork`/`Drop` are recursive
  functions.
- **No debug-mode call stack** (it was an IVM-only lazy stream); backtraces
  should come from frames later.
- **Every `~T` is one word**: a space pointing at a slot that holds a whole `T`,
  however large. (A tuple of spaces was rejected, as passing spaces to large
  values would be expensive.) Since the type system equates `~(A, B)` with
  `(~A, ~B)`, splitting a space is free (sub-spaces at offsets); combining
  spaces needs a small forwarding frame, which is rare.
- **The frame counter counts words still missing** (plus one if the code has not
  been supplied), not slots. This makes splitting spaces free.
- **Holes are frames whose code is supplied later.**
  `Hole::new[T]() -> (Hole[T], ~T)`: the write end is a plain `~T`; the
  `Hole[T]` read end supplies the code: `.get()`, `.forward(to: ~T)`,
  `Hole::of(v)`, `.as_ref()`. A hole has exactly one value slot. A hole's value
  may be read only once.
- **`List` stays a difference list**: `List(N32, Hole[Stream[T]], ~Stream[T])`,
  with `Stream = done() | more(T, Hole[Stream[T]])` (an `unsafe enum`, i.e. a
  union). A `Vec`-like type may come later.
- **Explicit `Box[T]`** controls what is heap-allocated vs. stored inline.
  Recursive types without a `Box` are a compile error ("infinite size"), as in
  Rust. `Box` is not self-dual. Values carry no tags.
- **Layout specialization without two phases**: every type parameter has a
  hidden `Layout[T]` implementation parameter, so the existing specializer
  (which specializes by implementations) specializes by layout.
- **Emitter**: one bytecode *unit* per specialization, holding all of its VIR
  stages; locals live in registers; units are entered through *blocks*. Calling
  convention: one slot per parameter, plus a return space unless the return type
  is empty. Constants are evaluated per use.
- **Waiting**: first a strict version (wait at the first use), then let pending
  values flow through locals, data and calls (directly into slots when the
  consumer is known, compiler-introduced holes otherwise). The second part is
  partly done; see [Waiting](#waiting).

### Open question: laziness of strict steps

Many test programs rely on IVM's evaluation order, where each node waits only
for its own inputs. The smallest example:

```vi
let i = 0;
let f = fn* () { let n = i; i += 1; n };
let g = f;                       // fork: f continues from g's final state
io.println("{f()} {g()} {i}");   // IVM prints "1 0 2"
```

`f()` can only finish after `g()`, but building the string waits for `f()`'s
text before `g()` is called, so frames deadlocks. Options:

- **A — detach strict steps**: when a strict step (string or list building, an
  operation) has inputs which aren't available yet, and its result is only
  passed on, compile it into its own small frame, so that only it waits. Close
  to IVM's semantics; costs a hole and a frame where it triggers.
- **B — accept a stricter order**: rewrite the stdlib functions and tests which
  rely on it. Cheaper and more predictable, but some valid programs deadlock.

The leaning was towards A, limited to that case. **This is not decided; ask Nils
before implementing either.**

## Architecture

### Pipeline

The frontend is unchanged up to VIR: charter, resolver (TIR), distiller (VIR),
normalizer (removes divergence and layers; creates continuation stages),
analyzer (interface wires `(input, barrier, output)` per local), specializer
(implementation arguments, `ImplTree`s, `SpecRels`). Then:

- `vine/src/features/layout.rs`: the hidden `Layout` parameters. While an item
  is resolved, `Layout[T]` queries are answered with `TirImpl::LayoutOf(ty)`
  (the type may not be inferred yet); `LayoutResolver` later replaces these with
  `TirImpl::Layout(LayoutKind, children)`. Derived impls and the automatic
  `Fork`/`Drop` impls get layout parameters too. Explicit impl arguments skip
  them; `show_generics` hides them.
- `vine/src/components/layouter.rs`: computes `Layout { size, plain }` (`size`
  in words). Box, Hole, spaces and closures are one non-plain word; an inverted,
  non-self-inverse type is a space; an enum is a tag word plus the largest
  variant; a union is its largest variant; a reference is the value plus a
  space. Reports infinite sizes, and `duplicate`/`erase` on non-plain data.
- `vine/src/components/frames.rs`: `FramesEmitter` compiles specializations on
  demand, starting from `main`, and builds the entry unit (which calls `main`
  with an IO handle, and halts once the final IO handle is written).
- `vine/src/components/frames/unit.rs`: compiles one specialization into a unit.
  Its module docs explain wires, waiting and control flow; read them.
- `frames/`: the runtime crate. `program.rs` (units, blocks, instructions),
  `runtime.rs` (the interpreter), `heap.rs` (a `Vec<u64>` with per-size free
  lists), `ops.rs` (primitive operations, from `vine_util::arithmetic`).
  `lib.rs` has an overview.
- `cli/src/vine_cli.rs`: `vine run --frames`; `vine build --target frames`
  prints the layouts the program uses.

### The runtime

- A *frame* is a header word (`counter << 48 | code`) followed by its words. It
  runs once all of its words have been written; its words are then loaded into
  the registers its block names, and it is freed.
- A *space* is `(frame << 16) | offset`. `Write` fills a slot through a space;
  `Split` makes sub-spaces, for free.
- There are no return values: callees write their result into a return space,
  which usually points into the caller's continuation frame.
- A *hole* is a frame with `CODE_NONE`. `HoleForward` supplies code that
  forwards the value into a space (`CODE_FORWARD | len`, with the space stored
  after the value); `HoleTake` takes the value if it has arrived; `HoleOf` makes
  a filled hole.
- A *unit* is code plus a register count; a *block* is
  `(unit, entry label, frame word → register map)`.
- Errors: `Panic`, `InvalidOp` (e.g. division by zero), `Deadlock` (frames left
  waiting when nothing is ready), `HoleMisuse` ("hole read more than once").

### Emitting a unit

- **Wires**: every VIR wire has a writer (a port whose type is inverted and not
  self-inverse) and a reader. Whichever end is emitted first records a state
  (`Value`, `ReaderLocal`, `ReaderSpace`, `LocalAtEnd`, `Discard`); the second
  completes the connection. Locals of space type have inverted roles.
- **Stages** are code in the unit. A transfer which is a stage's last step is a
  jump; an earlier transfer is like a call into a *child* stage chain, which
  returns to the step after it (`ReturnPoint::After`). Child stages only see the
  locals of their interface. Outputs of a stage's interface are preserved across
  jumps until control returns.
- Steps which only move data (composites, refs, rewraps, links, enums, unions)
  are deferred until their inputs exist, and until the readers of the spaces
  they create are known.
- **Final values**: a local read before it is written reads its value at the end
  of the scope (`LocalAtEnd`, and `at_end` write-backs).
- **Closures** are holes holding their environment: the values of captured
  locals, and spaces for the final values of the locals they modify. Their call,
  fork and drop stages are entry points of the unit, which take the environment
  from the hole (`HoleTake`, or wait for it).
- **Branches on constant booleans** only emit the stage taken.
- **Unsupported constructs** emit a runtime trap
  (`not yet supported by the
  frames backend: …`), since they may be in code
  never run (e.g. the debug branch of `if const debug::enabled`).
  `FRAMES_STRICT=1` makes them compile errors.

### Waiting

There are three kinds of values not available yet:

1. **Virtual**: a space for a value this unit will produce itself, which only
   exists at compile time; writing it just moves registers. It becomes real when
   it escapes (e.g. into a callee's frame).
2. **Pending**: the value will arrive in the current *continuation frame*.
   Reading it *suspends*: the live registers are saved into the continuation
   frame and the block ends, resuming once it is ready. Suspending waits for
   **all** pending values, which can deadlock if one of them only arrives later.
3. **Held**: the value is held by a hole. Writing it somewhere forwards the hole
   without waiting; only reading it waits (it then becomes pending). Values only
   passed on (into locals, calls, data or the result) are held; see `passed_on`.
   Locals returned from child stages which are only passed on are returned in
   fixed hole registers (`lazy_returns`), since the code after a return point is
   shared by every path.

## Status

Last updated 2026-10-15 (`tests/frames.sh`, 84 programs):

**28 of 84 pass.** Failing programs per error (a program can count more than
once):

| Programs | Error                                                                   |
| -------: | ----------------------------------------------------------------------- |
|       13 | deadlock (mostly the open question above)                               |
|       14 | `Nat` literals (12 of them through `Pcg32::canonical`)                  |
|        6 | hole read more than once                                                |
|        5 | infinite size (`cons`, `life`, `par`, `regex`, `unary` need a `Box`)    |
|        5 | inline Ivy (`F64::fork` ×3, `IO::args`, `IO::File::create`)             |
|        1 | inverted locals (`inverse`)                                             |
|        1 | a value used before it is computed (`configurable`)                     |
|        1 | invalid operands to `n32:div` (`div_by_zero`; expected output is IVM's) |
|        2 | emitter / heap panics (`lambda`, `centimanes`)                          |

The remaining failures have wrong output without an error (e.g. `sum_divisors`,
`mandelbrot`, `named_impls`, `nothing_lasts_forever`) and have not been
investigated yet.

Notes:

- Some expected outputs depend on IVM specifics (backtraces of the removed debug
  call stack, IVM's error messages), so a few programs can only pass once their
  snapshots are adapted.
- The open question above causes most deadlocks (e.g. forking closures with
  mutable captures, as in `array_order`).
- `Nat` literals are not supported (mostly hit through `Pcg32`).
- Remaining `$ivy` blocks (120 in `root`) are fine when their function is an
  `#[intrinsic]`; others (`F64::fork`, `IO::args`, `IO::File::create`, …) need
  intrinsics.
- Inverted locals are not supported.
- `cons`, `life`, `par`, `regex`, `unary` need a `Box` in their recursive types.
  Tests relying on erasure are marked `TODO(frames)`.
- Programs leak objects (the stats line reports them); hello world leaks none.

## Working on it

```sh
cargo build --release --bin vine
target/release/vine run --frames tests/programs/logic.vi
tests/frames.sh            # all programs, with a summary of failures
tests/frames.sh logic      # only names containing "logic"
```

Debugging environment variables:

- `FRAMES_DUMP=1`: print the compiled program (units, blocks, instructions).
- `FRAMES_TRACE=1`: print every block run, with its frame's words.
- `FRAMES_DEBUG=1`: add `(stage, step)` to unsupported messages, print stuck
  steps and each unit's entry points.
- `FRAMES_PANIC=1`: panic at the first unsupported construct (use with a debug
  build and `RUST_BACKTRACE=1`).
- `FRAMES_STRICT=1`: make unsupported constructs compile errors.
- `DUMP_VIR=<path suffix>`: print the VIR of fragments whose path ends with it,
  e.g. `DUMP_VIR=List::push_back`.

A typical loop: pick a failure from `tests/frames.sh`, shrink it into a small
program, look at its VIR (`DUMP_VIR`) and bytecode (`FRAMES_DUMP`), trace it
(`FRAMES_TRACE`), fix, and rerun the suite to check for regressions. Also run
`cargo clippy --all-targets`, `cargo fmt`, and the frames crate's tests
(`cargo test -p frames`).
