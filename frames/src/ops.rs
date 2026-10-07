//! Primitive operations on words.
//!
//! The arithmetic operations are defined by [`vine_util::arithmetic`], which is
//! shared with IVM, so that both runtimes agree on their semantics.

use std::collections::HashMap;

use vine_util::{
  arithmetic::{Define, arithmetic},
  register::{Register, Registry},
};

/// A primitive operation; reads its inputs from the start of the slice, and
/// pushes its outputs. Returns `Err` if the operation is invalid for its
/// inputs, e.g. division by zero.
pub type OpFn = Box<dyn Fn(&[u64], &mut Vec<u64>) -> Result<(), Invalid> + Send + Sync>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Invalid;

/// A primitive operation, with the number of words it reads and writes.
pub struct Op {
  pub name: &'static str,
  pub inputs: usize,
  pub outputs: usize,
  pub f: OpFn,
}

/// The table of primitive operations, keyed by name (e.g. `n32:add`).
pub struct Ops {
  pub ops: HashMap<&'static str, Op>,
}

impl Ops {
  pub fn new() -> Self {
    let mut ops = Ops { ops: HashMap::new() };
    Register::<Ops>::register(arithmetic(Invalid), &mut ops);
    ops.define_fn("vi:bool:and", |(a, b): (bool, bool)| a & b);
    ops.define_fn("vi:bool:or", |(a, b): (bool, bool)| a | b);
    ops.define_fn("vi:bool:xor", |(a, b): (bool, bool)| a ^ b);
    ops.define_fn("vi:bool:eq", |(a, b): (bool, bool)| a == b);
    ops.define_fn("vi:bool:le", |(a, b): (bool, bool)| a <= b);
    ops.define_fn("vi:bool:lt", |(a, b): (bool, bool)| !a & b);
    ops.define_fn("vi:bool:not", |a: bool| !a);
    ops.define_fn("vi:bool:to_n32", |a: bool| a as u32);
    ops
  }

  pub fn get(&self, name: &str) -> Option<&Op> {
    self.ops.get(name)
  }

  fn define_fn<I: Inputs, O: Outputs>(
    &mut self,
    name: &'static str,
    f: impl 'static + Send + Sync + Fn(I) -> O,
  ) {
    <Ops as Define<I, O, ()>>::define(self, name, f);
  }
}

impl Default for Ops {
  fn default() -> Self {
    Self::new()
  }
}

impl Registry for Ops {
  type Mut<'r>
    = &'r mut Ops
  where
    Self: 'r;
  fn fork<'a>(ops: &'a mut &mut Ops) -> &'a mut Ops {
    ops
  }
}

impl<I: Inputs, O: Outputs> Define<I, O, ()> for Ops {
  fn define(ops: &mut Ops, name: &'static str, f: impl 'static + Send + Sync + Fn(I) -> O) {
    // Strip the IVM namespace; intrinsics are named e.g. `n32:add`.
    let name = name.strip_prefix("vi:").unwrap_or(name);
    let f: OpFn = Box::new(move |inputs, outputs| f(I::read(inputs)).write(outputs));
    ops.ops.insert(name, Op { name, inputs: I::LEN, outputs: O::LEN, f });
  }
}

/// A value that can be read from words.
pub trait Inputs {
  const LEN: usize;
  fn read(words: &[u64]) -> Self;
}

/// A value that can be written as words.
pub trait Outputs {
  const LEN: usize;
  fn write(self, words: &mut Vec<u64>) -> Result<(), Invalid>;
}

macro_rules! word {
  ($($ty:ty: |$w:ident| $read:expr, |$v:ident| $write:expr;)*) => {$(
    impl Inputs for $ty {
      const LEN: usize = 1;
      fn read(words: &[u64]) -> Self {
        let $w = words[0];
        $read
      }
    }

    impl Outputs for $ty {
      const LEN: usize = 1;
      fn write(self, words: &mut Vec<u64>) -> Result<(), Invalid> {
        let $v = self;
        words.push($write);
        Ok(())
      }
    }
  )*};
}

word! {
  u32: |w| w as u32, |v| v as u64;
  bool: |w| w != 0, |v| v as u64;
  f32: |w| f32::from_bits(w as u32), |v| v.to_bits() as u64;
  f64: |w| f64::from_bits(w), |v| v.to_bits();
}

impl Outputs for () {
  const LEN: usize = 0;
  fn write(self, _: &mut Vec<u64>) -> Result<(), Invalid> {
    Ok(())
  }
}

impl<A: Inputs, B: Inputs> Inputs for (A, B) {
  const LEN: usize = A::LEN + B::LEN;
  fn read(words: &[u64]) -> Self {
    (A::read(words), B::read(&words[A::LEN..]))
  }
}

impl<A: Outputs, B: Outputs> Outputs for (A, B) {
  const LEN: usize = A::LEN + B::LEN;
  fn write(self, words: &mut Vec<u64>) -> Result<(), Invalid> {
    self.0.write(words)?;
    self.1.write(words)
  }
}

impl<T: Outputs> Outputs for Result<T, Invalid> {
  const LEN: usize = T::LEN;
  fn write(self, words: &mut Vec<u64>) -> Result<(), Invalid> {
    self?.write(words)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn run(ops: &Ops, name: &str, inputs: &[u64]) -> Result<Vec<u64>, Invalid> {
    let op = ops.get(name).unwrap();
    assert_eq!(op.inputs, inputs.len());
    let mut out = Vec::new();
    (op.f)(inputs, &mut out)?;
    assert_eq!(op.outputs, out.len());
    Ok(out)
  }

  #[test]
  fn arithmetic() {
    let ops = Ops::new();
    assert_eq!(run(&ops, "n32:add", &[u32::MAX as u64, 2]), Ok(vec![1]));
    assert_eq!(run(&ops, "n32:div", &[7, 0]), Err(Invalid));
    assert_eq!(run(&ops, "i32:lt", &[(-1i32) as u32 as u64, 0]), Ok(vec![1]));
    assert_eq!(run(&ops, "bool:not", &[0]), Ok(vec![1]));
    let f = |x: f64| x.to_bits();
    assert_eq!(run(&ops, "f64:add", &[f(1.5), f(2.0)]), Ok(vec![f(3.5)]));
    assert_eq!(run(&ops, "f64:to_bits", &[f(1.0)]), Ok(vec![0, 0x3ff00000]));
  }
}
