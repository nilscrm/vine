use class::Classes;
use ivy::{
  name::Table,
  net::{FlatNet, Wire},
};
use vine_util::{idx::IdxVec, nat::Nat, new_idx};

use crate::{
  components::synthesizer::SyntheticImpl,
  structures::{
    ast::{Flex, LogicalOp, Span},
    chart::{ConcreteConstId, EnumId, FnId, ImplId, OpaqueTypeId, StructId, UnionId, VariantId},
    diag::ErrorGuaranteed,
    resolutions::{ConstRelId, FnRelId, Rels},
    types::{TransferTypes, Type, TypeTransfer, Types},
  },
};

new_idx!(pub TargetId);
new_idx!(pub Local; n => ["l{n}"]);
new_idx!(pub ClosureId; n => ["c{n}"]);

#[derive(Debug, Clone)]
pub struct Tir {
  pub span: Span,
  pub types: Types,
  pub locals: IdxVec<Local, TirLocal>,
  pub rels: Rels,
  pub closures: IdxVec<ClosureId, TirClosure>,
  pub params: Option<Vec<TirPat>>,
  pub body: TirExpr,
}

#[derive(Debug, Clone)]
pub struct TirClosure {
  pub span: Span,
  pub ty: Type,
  pub flex: Flex,
  pub params: Vec<TirPat>,
  pub body: TirExpr,
}

#[derive(Debug, Clone)]
pub struct TirLocal {
  pub span: Span,
  pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct TirExpr {
  pub span: Span,
  pub ty: Type,
  pub kind: Box<TirExprKind>,
}

#[derive(Debug, Clone, Classes)]
pub enum TirExprKind {
  #[class(poly, value, space, place)]
  Hole,
  #[class(value)]
  Const(ConstRelId),
  #[class(value)]
  Fn,
  #[class(poly, value, place, space)]
  Local(Local),
  #[class(value)]
  Closure(ClosureId),
  #[class(value)]
  Do(TargetId, TirExpr),
  #[class(nil, value)]
  Assign(bool, TirExpr, TirExpr),
  #[class(value)]
  Match(TirExpr, Vec<(TirPat, TirExpr)>),
  #[class(value)]
  If(TirExpr, TirExpr, Option<TirExpr>),
  #[class(value)]
  When(TargetId, Vec<(TirExpr, TirExpr)>, Option<TirExpr>),
  #[class(value)]
  While(TargetId, TirExpr, TirExpr, Option<TirExpr>),
  #[class(value)]
  Loop(TargetId, TirExpr),
  #[class(value)]
  For(TargetId, FnRelId, TirPat, TirExpr, TirExpr, Option<TirExpr>),
  #[class(nil, value)]
  Return(Option<TirExpr>),
  #[class(nil, value)]
  Break(TargetId, Option<TirExpr>),
  #[class(nil, value)]
  Continue(TargetId),
  #[class(value)]
  Ref(TirExpr),
  #[class(place)]
  Deref(TirExpr),
  #[class(poly, value, place, space)]
  Inverse(TirExpr),
  #[class(place)]
  Place(TirExpr, TirExpr),
  #[class(poly, value, place, space)]
  Composite(Vec<TirExpr>),
  #[class(value)]
  List(Vec<TirExpr>),
  #[class(poly)]
  Field(TirExpr, usize, Vec<Type>),
  #[class(value)]
  Call(FnRelId, Vec<TirExpr>),
  #[class(poly, value, space, place)]
  Index(TirExpr, TirExpr),
  #[class(poly, value, place, space)]
  Rewrap(TirExpr),
  #[class(value)]
  Enum(EnumId, VariantId, TirExpr),
  #[class(value, cond)]
  Bool(bool),
  #[class(value, cond)]
  Not(TirExpr),
  #[class(value, cond)]
  Is(TirExpr, TirPat),
  #[class(value, cond)]
  LogicalOp(LogicalOp, TirExpr, TirExpr),
  #[class(value)]
  Try(Type, Type, TirExpr),
  #[class(value)]
  N32(u32),
  #[class(value)]
  F32(f32),
  #[class(value)]
  F64(f64),
  #[class(value)]
  Nat(Nat),
  #[class(value)]
  Char(char),
  #[class(value)]
  String(String, Vec<(TirExpr, String)>),
  #[class(value)]
  InlineIvy(Table, FlatNet, Vec<(Wire, TirExpr)>),
  #[class(nil, value)]
  CallAssign(FnRelId, TirExpr, TirExpr),
  #[class(value)]
  CallCompare(TirExpr, Vec<(FnRelId, TirExpr)>),
  #[class(value)]
  Let(TirPat, TirExprLetKind, TirExpr),
  #[class(value)]
  Seq(TirExpr, TirExpr),
  #[class(poly, value, place, space)]
  Error(ErrorGuaranteed),
}

#[derive(Debug, Clone)]
pub enum TirExprLetKind {
  Init(TirExpr),
  Uninit,
  Loop,
}

#[derive(Debug, Clone)]
pub struct TirPat {
  pub span: Span,
  pub ty: Type,
  pub kind: Box<TirPatKind>,
}

#[derive(Debug, Clone, Classes)]
pub enum TirPatKind {
  #[class(value, place, space, complete)]
  Hole,
  #[class(value, place, space, complete, incomplete)]
  Struct(TirPat),
  #[class(value, place, space, incomplete)]
  Enum(EnumId, VariantId, TirPat),
  #[class(value, place, space, complete)]
  Union(TirPat),
  #[class(value, place, space, complete)]
  Local(Local),
  #[class(value, place, complete, incomplete)]
  Ref(TirPat),
  #[class(place, complete)]
  Deref(TirPat),
  #[class(value, place, space, complete)]
  Inverse(TirPat),
  #[class(value, place, space, complete, incomplete)]
  Composite(Vec<TirPat>),
  #[class(value, place, space, complete)]
  Error(ErrorGuaranteed),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TirImpl {
  Error(ErrorGuaranteed),
  Param(usize),
  Def(ImplId, Vec<TirImpl>),
  Fn(FnId, Vec<TirImpl>, usize),
  Closure(ClosureId),
  ForkClosure(ClosureId),
  DropClosure(ClosureId),
  Synthetic(SyntheticImpl),
  /// The layout of a type in the current fragment's type context; only used
  /// during resolution, until types have been inferred, after which it is
  /// replaced with [`TirImpl::Layout`].
  LayoutOf(Type),
  /// A layout, with the layouts of the type's parameters (or fields).
  Layout(LayoutKind, Vec<TirImpl>),
}

/// The kind of a layout; see [`TirImpl::Layout`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LayoutKind {
  /// No data; e.g. nil, functions, and `!`.
  Empty,
  /// A space.
  Space,
  /// A tuple or object; the children are the layouts of its fields.
  Composite,
  Struct(StructId),
  Enum(EnumId),
  Union(UnionId),
  Opaque(OpaqueTypeId),
  /// The layout of a type that depends on a constant: the children are the
  /// layouts of the two branches, laid out like an untagged union.
  IfConst(ConcreteConstId),
  /// A reference: a value, followed by a space.
  Ref,
  /// A closure: a pointer to its captured state.
  Closure,
}

impl TransferTypes for TirImpl {
  fn transfer(&self, t: &mut TypeTransfer<'_>) -> Self {
    match self {
      TirImpl::Def(id, impls) => TirImpl::Def(*id, t.transfer(impls)),
      TirImpl::Fn(id, impls, params) => TirImpl::Fn(*id, t.transfer(impls), *params),
      TirImpl::LayoutOf(ty) => TirImpl::LayoutOf(t.transfer(ty)),
      TirImpl::Layout(kind, children) => TirImpl::Layout(kind.clone(), t.transfer(children)),
      TirImpl::Error(_)
      | TirImpl::Param(_)
      | TirImpl::Closure(_)
      | TirImpl::ForkClosure(_)
      | TirImpl::DropClosure(_)
      | TirImpl::Synthetic(_) => self.clone(),
    }
  }
}

impl TirExpr {
  pub fn new(span: Span, ty: Type, kind: TirExprKind) -> Self {
    TirExpr { span, ty, kind: Box::new(kind) }
  }
}

impl TirPat {
  pub fn new(span: Span, ty: Type, kind: TirPatKind) -> Self {
    TirPat { span, ty, kind: Box::new(kind) }
  }
}
