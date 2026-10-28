use std::fmt;

macro_rules! intrinsics {
  ($($variant:ident = $name:literal,)*) => {
    /// An operation implemented directly by the backend, rather than in Vine.
    ///
    /// Intrinsics are attached to functions with `#[intrinsic = "name"]`; the
    /// function's signature describes the operation's inputs and outputs.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum Intrinsic {
      $($variant,)*
    }

    impl Intrinsic {
      pub fn from_name(name: &str) -> Option<Intrinsic> {
        match name {
          $($name => Some(Intrinsic::$variant),)*
          _ => None,
        }
      }

      pub fn name(self) -> &'static str {
        match self {
          $(Intrinsic::$variant => $name,)*
        }
      }
    }
  };
}

intrinsics! {
  Duplicate = "duplicate",
  Transmute = "transmute",
  BlackBox = "black_box",
  Erase = "erase",
  Forget = "forget",
  Unreachable = "unreachable",
  Panic = "panic",

  N32Add = "n32:add",
  N32Sub = "n32:sub",
  N32Mul = "n32:mul",
  N32Div = "n32:div",
  N32Rem = "n32:rem",
  N32And = "n32:and",
  N32Or = "n32:or",
  N32Xor = "n32:xor",
  N32Shl = "n32:shl",
  N32Shr = "n32:shr",
  N32Rotl = "n32:rotl",
  N32Rotr = "n32:rotr",
  N32Eq = "n32:eq",
  N32Ne = "n32:ne",
  N32Lt = "n32:lt",
  N32Le = "n32:le",
  N32AddHigh = "n32:add_high",
  N32MulHigh = "n32:mul_high",
  N32ToF32 = "n32:to_f32",
  N32ToF64 = "n32:to_f64",

  I32Div = "i32:div",
  I32Rem = "i32:rem",
  I32Shr = "i32:shr",
  I32Lt = "i32:lt",
  I32Le = "i32:le",
  I32ToF32 = "i32:to_f32",
  I32ToF64 = "i32:to_f64",

  N64ToF64 = "n64:to_f64",

  F32Add = "f32:add",
  F32Sub = "f32:sub",
  F32Mul = "f32:mul",
  F32Div = "f32:div",
  F32Rem = "f32:rem",
  F32Sqrt = "f32:sqrt",
  F32Eq = "f32:eq",
  F32Ne = "f32:ne",
  F32Lt = "f32:lt",
  F32Le = "f32:le",
  F32ToN32 = "f32:to_n32",
  F32ToI32 = "f32:to_i32",
  F32ToF64 = "f32:to_f64",
  F32ToBits = "f32:to_bits",
  F32FromBits = "f32:from_bits",

  F64Add = "f64:add",
  F64Sub = "f64:sub",
  F64Mul = "f64:mul",
  F64Div = "f64:div",
  F64Rem = "f64:rem",
  F64Sqrt = "f64:sqrt",
  F64Eq = "f64:eq",
  F64Ne = "f64:ne",
  F64Lt = "f64:lt",
  F64Le = "f64:le",
  F64ToN32 = "f64:to_n32",
  F64ToI32 = "f64:to_i32",
  F64ToF32 = "f64:to_f32",
  F64ToN64 = "f64:to_n64",
  F64ToBits = "f64:to_bits",
  F64FromBits = "f64:from_bits",
  F64Fork = "f64:fork",
  F64Drop = "f64:drop",

  BoolAnd = "bool:and",
  BoolOr = "bool:or",
  BoolXor = "bool:xor",
  BoolNot = "bool:not",
  BoolEq = "bool:eq",
  BoolLt = "bool:lt",
  BoolLe = "bool:le",
  BoolToN32 = "bool:to_n32",

  FrameNew = "frame:new",
  FrameOf = "frame:of",
  FrameGet = "frame:get",
  FrameForward = "frame:forward",
  FrameAsRef = "frame:as_ref",

  IoPrintChar = "io:print_char",
  IoPrintByte = "io:print_byte",
  IoFlush = "io:flush",
  IoReadChar = "io:read_char",
  IoReadByte = "io:read_byte",
  IoReady = "io:ready",
}

impl fmt::Display for Intrinsic {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str(self.name())
  }
}
