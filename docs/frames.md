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
  Rust. `Box` is not self-dual. Values carry no tags. A box is a hole holding
  its contents, so boxing and unboxing never wait.
- **No debug mode on frames**: `debug::enabled` (`#[builtin = "debug_enabled"]`)
  is `false`, both for `if const` branches and for the layout of `if const`
  types, which is that of the `else` branch.
- **Layout specialization without two phases**: every type parameter has a
  hidden `Layout[T]` implementation parameter, so the existing specializer
  (which specializes by implementations) specializes by layout.
- **Emitter**: one bytecode *unit* per specialization, holding all of its VIR
  stages; locals live in registers; units are entered through *blocks*. Calling
  convention: one slot per parameter, plus a return space unless the return type
  is empty. Constants are evaluated per use.
- **Waiting is dataflow** (decided 2026-10-17, settling the laziness
  question in favour of detaching): a step waits only for its own inputs. A
  step which reads values that are not available yet is emitted into a *task*,
  a small frame of the same unit, and the code emitting it goes on; values whose
  reader is not known yet are held in holes. Only control flow waits: a branch
  or match on a value that is not available yet, and locals passed to another
  stage (except those produced after the transfer, which are passed in holes).
  See [Waiting](#waiting). Steps which only wait for values one task computes
  are emitted into that task, and values are written directly into the frames
  of the tasks reading them where possible.
- **Limits of dataflow on frames**, where the standard library is adapted
  instead:
  - A frame waits for all of its words, so a match on an enum waits for its
    payload too, and a value written through one space arrives all at once.
    E.g. `IterRef::advance` borrows a stream's head and tail with one `as_ref`
    (`Stream::head_tail`), as borrowing the tail second would wait for the head
    to be released.
  - Control flow cannot wait for a value produced after it (e.g. a branch on a
    `let loop` value inside the loop that computes it); `format_comma_sep`
    formats its entries first, then decides on the layout.

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
  locals of their interface. The outputs of the interface a chain of stages was
  entered through are *owed*: kept across final transfers, and returned once
  control returns.
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

There are four kinds of values not available yet:

1. **Virtual**: a space for a value this unit will produce itself, which only
   exists at compile time; writing it just moves registers. It becomes real
   when it escapes (e.g. into a callee's frame), or at a stage boundary; its
   value is then held.
2. **Held**: the value is held by a hole. Writing it into a space forwards the
   hole; moving it only changes which registers the hole's words belong in. A
   hole whose words are used separately is split by a task (`align_holes`).
3. **In a task**: a step which reads values which are not available (an
   operation, building a string or list, an IO call, ...) is emitted by
   `emit_detached` into a task: the main code fills the task's frame with the
   step's inputs (forwarding holes, or pointing virtual spaces into it), and
   the step's code runs in the task once they have all arrived. Tasks stay
   *open* until the block filling their frames ends (`close_tasks`):
   - Values a step computes stay in its task (`in_task`). A later step whose
     waiting inputs are all computed by one open task is emitted into that
     task (`task_of`), which then waits for nothing more; this groups steps by
     the values they wait for.
   - Where a value computed by a task is used elsewhere, the task writes it
     there: into a callee's frame, another task's frame, or a space
     (`task_write`); into a hole if it is still used when the task closes
     (`release`).
   - A call's result which a later step of the block reads is written
     directly into the frame of the task that step is emitted into
     (`reader_tasks`); one which the next transfer waits for arrives in the
     continuation frame (`awaited_by_transfer`).

   Operations write references back before they wait, since they do not
   change them. Copies of values which are not available yet, writes into
   spaces which are not, and unboxing a box which is not are one-off tasks.
4. **Pending**: control flow which needs a value (a branch condition, the data
   matched on, a closure's environment, locals passed to another stage)
   *suspends*: the values it needs are forwarded into a *continuation frame*,
   along with the live registers, and the block ends. Nothing else is pending,
   so this waits only for what the control flow needs.

At a transfer, locals whose values are produced by code after it (read before
they are written, or borrowed by a reference the target takes), or which came
into the stage in holes, are passed in holes in fixed registers
(`lazy_inputs`), which all transfers into an interface agree on. Locals
returned from child stages which are only passed on are returned in holes too
(`lazy_returns`).

## Status

Last updated 2026-10-18 (`tests/frames.sh`, 84 programs):

**53 of 84 pass.** Failing programs per error (a program can count more than
once):

| Programs | Error                                                                   |
| -------: | ----------------------------------------------------------------------- |
|        7 | inline Ivy (`F64::fork` ×5, `IO::args`, `IO::File::create`)             |
|        6 | inverted locals (`List::trim_back_where`, `Nat::div_rem`, `inverse`)    |
|        5 | infinite size (`cons`, `life`, `par`, `regex`, `unary` need a `Box`)    |
|        2 | deadlock (`array_smoothsort`, `sort`)                                   |
|        2 | panics in the program (`opaque`: transmute of 0 words into 1; `option_party`) |
|        1 | invalid operands to `n32:div` (`div_by_zero`; expected output is IVM's) |

The remaining failures have no error: `lambda`, `iterator_party`,
`segmented_sieve` and `nothing_lasts_forever` time out or print wrong output;
`f32_ops`, `invalid_extrinsics`, `mandelbrot_sixel` and `mandelbrot_tga` print
wrong output (some snapshots may be IVM-specific). None of these have been
investigated yet.

Notes:

- Some expected outputs depend on IVM specifics (backtraces of the removed debug
  call stack, IVM's error messages), so a few programs can only pass once their
  snapshots are adapted.
- Performance: programs which also passed before the dataflow rewrite now run
  fewer instructions and frames than they did then (e.g. `fib` 88k
  instructions and 3.4k frames, from 102k and 7.1k; `sieve` 866M, from 1293M).
  Besides grouping, this comes from discarding values through a null space
  instead of a frame, skipping calls without inputs or outputs to functions
  which only move data (e.g. dropping `()`), and inlining constants which are
  literal words (e.g. `debug::enabled`). The largest remaining costs are calls
  to small wrappers (e.g. `N32::div`, `Lt::gt`), which are not inlined, and
  the holes returning values from child stages (`lazy_returns`).
- Remaining `$ivy` blocks (120 in `root`) are fine when their function is an
  `#[intrinsic]`; others (`F64::fork`, `IO::args`, `IO::File::create`, …) need
  intrinsics.
- Inverted locals are not supported.
- `cons`, `life`, `par`, `regex`, `unary` need a `Box` in their recursive types.
  Tests relying on erasure are marked `TODO(frames)`.
- Passing programs leak no objects, except `empty_loop` and `log_brute` (as
  before).

## Working on it

```sh
cargo build --release --bin vine
target/release/vine run --frames tests/programs/logic.vi
tests/frames.sh            # all programs, with a summary of failures
tests/frames.sh logic      # only names containing "logic"
```

Debugging environment variables:

- `FRAMES_DUMP=1`: print the compiled program (units, blocks, instructions).
- `FRAMES_TRACE=1`: print every block run, with its frame's words; report
  holes used with the wrong size and writes into objects which are not waiting;
  on a deadlock or leak, list the frames and holes still waiting (holes with
  where they were created).
- `FRAMES_PROFILE=1`: count how often each block runs and how many frames and
  holes each instruction creates, and print the top ones.
- `FRAMES_CHECK=1`: report blocks which read registers that are neither loaded
  from their frame nor written earlier (usually an emitter bug).
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
