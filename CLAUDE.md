# Vine: frames branch

This branch builds a new runtime for Vine based on *frames*, replacing IVM.
**Read `docs/frames.md` first**: it has the design decisions, the architecture,
the current status, and how to debug.

## Rules

- Don't keep compatibility with IVM; make the best choice for frames. The
  standard library (`root/`) may be rewritten freely.
- Don't revisit the decisions in `docs/frames.md` without asking Nils. In
  particular, the laziness question (detaching strict steps vs. a stricter
  evaluation order) is open: ask before implementing either.
- Keep `docs/frames.md` up to date: update its status section (from
  `tests/frames.sh`) and any affected design notes in the same commit as the
  change.
- Match the surrounding code: comment density, naming, and doc comments on
  items. Prefer clear, explicit code over cleverness.

## Workflow

1. `tests/frames.sh` to see what fails, and why.
2. Pick a failure, shrink it into a small program, and debug it with the
   environment variables listed in `docs/frames.md`.
3. Fix it, then rerun `tests/frames.sh` to check that nothing regressed.
4. `cargo fmt`, `cargo clippy --all-targets`, `cargo test -p frames`.
5. Commit with a message in the repo's style (`vine: …`, `frames: …`, `root: …`;
   an imperative summary, then a body explaining why).
