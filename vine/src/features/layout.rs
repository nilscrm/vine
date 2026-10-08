//! Layouts of types, used to specialize code for the layouts of its type
//! parameters.
//!
//! Every type parameter of an item that can have implementation parameters
//! has an implicit `Layout` implementation parameter (see
//! `Resolver::resolve_impl_params`). While an item is being resolved, the
//! finder answers queries for `Layout[T]` with [`TirImpl::LayoutOf`], since
//! `T` may not have been inferred yet; once it has been, [`LayoutResolver`]
//! replaces these with [`TirImpl::Layout`], which describes the layout in terms
//! of the item's own `Layout` parameters.

use crate::structures::{
  ast::Span,
  chart::{Chart, GenericsId},
  diag::{Diag, Diags, ErrorGuaranteed},
  resolutions::Rels,
  signatures::Signatures,
  tir::{LayoutKind, TirImpl},
  types::{ImplType, Type, TypeKind, Types},
};

pub(crate) struct LayoutResolver<'a> {
  chart: &'a Chart,
  diags: &'a mut Diags,
  types: &'a mut Types,
  span: Span,
  /// For each type parameter, the index of its `Layout` implementation
  /// parameter.
  params: Vec<Option<usize>>,
}

impl<'a> LayoutResolver<'a> {
  pub(crate) fn new(
    chart: &'a Chart,
    sigs: &Signatures,
    diags: &'a mut Diags,
    types: &'a mut Types,
    generics: GenericsId,
    span: Span,
  ) -> Self {
    let mut params = vec![None; sigs.type_params[generics].params.len()];
    let impl_params = &sigs.impl_params[generics].types;
    for (index, ty) in impl_params.inner.iter().enumerate() {
      if let ImplType::Trait(trait_id, tys) = ty
        && Some(*trait_id) == chart.builtins.layout
        && let Some((_, TypeKind::Param(param, _))) = impl_params.types.kind(tys[0])
      {
        params[*param] = Some(index);
      }
    }
    LayoutResolver { chart, diags, types, span, params }
  }

  pub(crate) fn resolve_rels(&mut self, rels: &mut Rels) {
    for (_, impls) in rels.fns.values_mut() {
      for impl_ in impls {
        self.resolve_impl(impl_);
      }
    }
    for (_, impls) in rels.consts.values_mut() {
      for impl_ in impls {
        self.resolve_impl(impl_);
      }
    }
  }

  /// Replaces every [`TirImpl::LayoutOf`] within `impl_`.
  pub(crate) fn resolve_impl(&mut self, impl_: &mut TirImpl) {
    match impl_ {
      TirImpl::LayoutOf(ty) => *impl_ = self.layout_of(*ty),
      TirImpl::Def(_, impls) | TirImpl::Fn(_, impls, _) | TirImpl::Layout(_, impls) => {
        for impl_ in impls {
          self.resolve_impl(impl_);
        }
      }
      TirImpl::Error(_)
      | TirImpl::Param(_)
      | TirImpl::Closure(_)
      | TirImpl::ForkClosure(_)
      | TirImpl::DropClosure(_)
      | TirImpl::Synthetic(_) => {}
    }
  }

  fn layout_of(&mut self, ty: Type) -> TirImpl {
    // Report any inference failure.
    self.types.force_kind(self.diags, ty);
    match shape(self.types, ty) {
      Shape::Param(index) => {
        match self.params.get(index).copied().flatten() {
          Some(param) => TirImpl::Param(param),
          None => TirImpl::Error(self.diags.error(Diag::LayoutUnavailable {
            span: self.span,
            ty: self.types.show(self.chart, ty),
          })),
        }
      }
      Shape::Node(kind, tys) => {
        TirImpl::Layout(kind, tys.into_iter().map(|ty| self.layout_of(ty)).collect())
      }
      Shape::Error(err) => TirImpl::Error(err),
    }
  }
}

/// The shape of a type's layout: either a type parameter, or a kind of layout
/// whose children are the layouts of the given types.
pub(crate) enum Shape {
  Param(usize),
  Node(LayoutKind, Vec<Type>),
  Error(ErrorGuaranteed),
}

/// Determines the shape of the layout of `ty`.
///
/// A space is a single word, so all inverted types have the same layout,
/// except for those which are their own inverse; these hold no data.
pub(crate) fn shape(types: &Types, ty: Type) -> Shape {
  let Some((inv, kind)) = types.kind(ty) else {
    return Shape::Error(ErrorGuaranteed::new_unchecked());
  };
  if inv.0 && !types.self_inverse(ty) {
    return Shape::Node(LayoutKind::Space, vec![]);
  }
  let node = |kind, tys: &[Type]| Shape::Node(kind, tys.iter().map(|t| t.invert_if(inv)).collect());
  match kind {
    TypeKind::Param(index, _) => Shape::Param(*index),
    TypeKind::Tuple(tys) => node(LayoutKind::Composite, tys),
    TypeKind::Object(entries) => {
      node(LayoutKind::Composite, &entries.values().copied().collect::<Vec<_>>())
    }
    TypeKind::Struct(id, _, tys) => node(LayoutKind::Struct(*id), tys),
    TypeKind::Enum(id, tys) => node(LayoutKind::Enum(*id), tys),
    TypeKind::Union(id, _, tys) => node(LayoutKind::Union(*id), tys),
    TypeKind::Opaque(id, tys) => node(LayoutKind::Opaque(*id), tys),
    TypeKind::Ref(ty) => node(LayoutKind::Ref, &[*ty]),
    TypeKind::Closure(..) => node(LayoutKind::Closure, &[]),
    TypeKind::IfConst(id, then, else_) => node(LayoutKind::IfConst(*id), &[*then, *else_]),
    TypeKind::Fn(_) | TypeKind::Key(_) | TypeKind::Never | TypeKind::Default => {
      node(LayoutKind::Empty, &[])
    }
    TypeKind::Error(err) => Shape::Error(*err),
  }
}
