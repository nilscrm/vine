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
  diag::{Diag, Diags},
  resolutions::Rels,
  signatures::Signatures,
  tir::{LayoutKind, TirImpl},
  types::{ImplType, Inverted, Type, TypeKind, Types},
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
    let (inv, kind) = self.types.force_kind(self.diags, ty);
    let kind = kind.clone();
    if inv.0 && !self.types.self_inverse(ty) {
      return TirImpl::Layout(LayoutKind::Space, vec![]);
    }
    let inv = if inv.0 { Inverted(true) } else { Inverted(false) };
    let children = |self_: &mut Self, tys: &[Type]| {
      tys.iter().map(|&t| self_.layout_of(t.invert_if(inv))).collect::<Vec<_>>()
    };
    match kind {
      TypeKind::Param(index, _) => {
        match self.params.get(index).copied().flatten() {
          Some(param) => TirImpl::Param(param),
          None => TirImpl::Error(self.diags.error(Diag::LayoutUnavailable {
            span: self.span,
            ty: self.types.show(self.chart, ty),
          })),
        }
      }
      TypeKind::Tuple(tys) => TirImpl::Layout(LayoutKind::Composite, children(self, &tys)),
      TypeKind::Object(entries) => {
        let tys = entries.values().copied().collect::<Vec<_>>();
        TirImpl::Layout(LayoutKind::Composite, children(self, &tys))
      }
      TypeKind::Struct(id, _, tys) => TirImpl::Layout(LayoutKind::Struct(id), children(self, &tys)),
      TypeKind::Enum(id, tys) => TirImpl::Layout(LayoutKind::Enum(id), children(self, &tys)),
      TypeKind::Union(id, _, tys) => TirImpl::Layout(LayoutKind::Union(id), children(self, &tys)),
      TypeKind::Opaque(id, tys) => TirImpl::Layout(LayoutKind::Opaque(id), children(self, &tys)),
      TypeKind::Ref(ty) => TirImpl::Layout(LayoutKind::Ref, children(self, &[ty])),
      TypeKind::Closure(..) => TirImpl::Layout(LayoutKind::Closure, vec![]),
      TypeKind::Fn(_) | TypeKind::Key(_) | TypeKind::Never | TypeKind::Default => {
        TirImpl::Layout(LayoutKind::Empty, vec![])
      }
      TypeKind::IfConst(id, then, else_) => {
        TirImpl::Layout(LayoutKind::IfConst(id), children(self, &[then, else_]))
      }
      TypeKind::Error(err) => TirImpl::Error(err),
    }
  }
}
