//! Computes the concrete layouts of values, as used by the frames runtime.

use std::collections::HashMap;

use frames::layout::{Field, Layout, LayoutId, Layouts};

use crate::{
  features::layout::{Shape, shape},
  structures::{
    chart::{Chart, DefId, OpaqueTypeId},
    diag::{Diag, Diags, ErrorGuaranteed},
    signatures::Signatures,
    specializations::{ImplTreeId, ImplTreeKind, Specializations},
    tir::LayoutKind,
    types::{Type, Types},
  },
};

/// A layout, described structurally: the kind of layout, and the layouts of
/// the type's parameters (or fields).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Term(pub LayoutKind, pub Vec<Term>);

#[derive(Debug, Clone, Copy)]
enum State {
  /// Its layout is being computed; encountering it again (except within a
  /// `Box`) means that it has infinite size.
  InProgress(LayoutId),
  /// Its layout has been requested within a `Box`, and will be computed later.
  Pending(LayoutId),
  Done(Result<LayoutId, ErrorGuaranteed>),
}

pub struct Layouter<'a> {
  chart: &'a Chart,
  sigs: &'a Signatures,
  specs: &'a Specializations,
  diags: &'a mut Diags,
  pub layouts: Layouts,
  states: HashMap<Term, State>,
  pending: Vec<(LayoutId, Term)>,
  /// Types already reported to have infinite size, with the error reported.
  infinite: HashMap<DefId, ErrorGuaranteed>,
}

impl<'a> Layouter<'a> {
  pub fn new(
    chart: &'a Chart,
    sigs: &'a Signatures,
    specs: &'a Specializations,
    diags: &'a mut Diags,
  ) -> Self {
    Layouter {
      chart,
      sigs,
      specs,
      diags,
      layouts: Layouts::default(),
      states: HashMap::new(),
      pending: Vec::new(),
      infinite: HashMap::new(),
    }
  }

  /// Returns the layout described by an implementation of `Layout`.
  pub fn impl_tree_layout(&mut self, tree: ImplTreeId) -> Result<LayoutId, ErrorGuaranteed> {
    let term = self.impl_tree_term(tree)?;
    self.term_layout(term)
  }

  /// Returns the layout of a type, given the layouts of its type parameters.
  pub fn type_layout(
    &mut self,
    types: &Types,
    ty: Type,
    params: &[Term],
  ) -> Result<LayoutId, ErrorGuaranteed> {
    let term = self.type_term(types, ty, params)?;
    self.term_layout(term)
  }

  pub fn impl_tree_term(&self, tree: ImplTreeId) -> Result<Term, ErrorGuaranteed> {
    match &self.specs.impls[tree].kind {
      ImplTreeKind::Layout(kind, children) => Ok(Term(
        kind.clone(),
        children.iter().map(|&child| self.impl_tree_term(child)).collect::<Result<_, _>>()?,
      )),
      ImplTreeKind::Error(err) => Err(*err),
      kind => unreachable!("expected a layout, found {kind:?}"),
    }
  }

  fn type_term(&self, types: &Types, ty: Type, params: &[Term]) -> Result<Term, ErrorGuaranteed> {
    match shape(types, ty) {
      Shape::Param(index) => Ok(params[index].clone()),
      Shape::Node(kind, tys) => Ok(Term(
        kind,
        tys.into_iter().map(|ty| self.type_term(types, ty, params)).collect::<Result<_, _>>()?,
      )),
      Shape::Error(err) => Err(err),
    }
  }

  pub fn term_layout(&mut self, term: Term) -> Result<LayoutId, ErrorGuaranteed> {
    let result = self.term_layout_now(term);
    self.flush();
    result
  }

  /// Computes the layout of `term`, which must have a finite size.
  fn term_layout_now(&mut self, term: Term) -> Result<LayoutId, ErrorGuaranteed> {
    match self.states.get(&term) {
      Some(State::Done(result)) => *result,
      Some(State::InProgress(_)) => Err(self.infinite_size(&term)),
      Some(&State::Pending(id)) => self.compute(id, term),
      None => {
        let id = self.layouts.reserve();
        self.compute(id, term)
      }
    }
  }

  /// Returns an id for the layout of `term`, which may be computed later; used
  /// for the contents of a `Box`, which do not affect its size.
  fn term_layout_later(&mut self, term: Term) -> Result<LayoutId, ErrorGuaranteed> {
    match self.states.get(&term) {
      Some(State::Done(result)) => *result,
      Some(&State::InProgress(id) | &State::Pending(id)) => Ok(id),
      None => {
        let id = self.layouts.reserve();
        self.states.insert(term.clone(), State::Pending(id));
        self.pending.push((id, term));
        Ok(id)
      }
    }
  }

  fn flush(&mut self) {
    while let Some((id, term)) = self.pending.pop() {
      if let Some(State::Pending(_)) = self.states.get(&term) {
        _ = self.compute(id, term);
      }
    }
  }

  fn compute(&mut self, id: LayoutId, term: Term) -> Result<LayoutId, ErrorGuaranteed> {
    self.states.insert(term.clone(), State::InProgress(id));
    let result = self.compute_layout(&term).map(|layout| {
      self.layouts.define(id, layout);
      id
    });
    self.states.insert(term, State::Done(result));
    result
  }

  fn compute_layout(&mut self, Term(kind, children): &Term) -> Result<Layout, ErrorGuaranteed> {
    Ok(match kind {
      LayoutKind::Empty => Layout::EMPTY,
      LayoutKind::Space => opaque("a space"),
      LayoutKind::Closure => opaque("a closure"),
      LayoutKind::Composite => self.concat(children.iter().cloned())?,
      LayoutKind::Ref => {
        let mut layout = self.concat(children.iter().cloned())?;
        layout.fields.push(Field::Opaque { offset: layout.size, what: "a space" });
        layout.size += 1;
        layout
      }
      LayoutKind::Opaque(id) => self.opaque_layout(*id),
      LayoutKind::Struct(id) if Some(*id) == self.chart.builtins.box_ => {
        let layout = self.term_layout_later(children[0].clone())?;
        Layout { size: 1, fields: vec![Field::Box { offset: 0, layout }] }
      }
      LayoutKind::Struct(id) => {
        let sig = &self.sigs.structs[*id];
        let term = self.type_term(&sig.types, sig.inner.data, children)?;
        let content = self.term_layout_now(term)?;
        self.layouts.layouts[content].clone()
      }
      LayoutKind::Enum(id) => {
        let sig = &self.sigs.enums[*id];
        let variants = sig
          .inner
          .variant_data
          .values()
          .map(|&ty| {
            let term = self.type_term(&sig.types, ty, children)?;
            self.term_layout_now(term)
          })
          .collect::<Result<Vec<_>, _>>()?;
        let size = 1 + self.max_size(&variants);
        let plain = variants.iter().all(|&v| self.layouts.layouts[v].is_plain());
        let fields = if plain { vec![] } else { vec![Field::Enum { offset: 0, variants }] };
        Layout { size, fields }
      }
      LayoutKind::Union(id) => {
        let sig = &self.sigs.unions[*id];
        let variants = sig
          .inner
          .variant_data
          .values()
          .map(|&ty| {
            let term = self.type_term(&sig.types, ty, children)?;
            self.term_layout_now(term)
          })
          .collect::<Result<Vec<_>, _>>()?;
        self.union(&variants)
      }
      LayoutKind::IfConst(_) => {
        let branches = children
          .iter()
          .map(|child| self.term_layout_now(child.clone()))
          .collect::<Result<Vec<_>, _>>()?;
        self.union(&branches)
      }
    })
  }

  /// Lays out values one after another.
  fn concat(&mut self, terms: impl Iterator<Item = Term>) -> Result<Layout, ErrorGuaranteed> {
    let mut layout = Layout::EMPTY;
    for term in terms {
      let id = self.term_layout_now(term)?;
      let part = &self.layouts.layouts[id];
      if !part.is_plain() {
        layout.fields.push(Field::Inline { offset: layout.size, layout: id });
      }
      layout.size += part.size;
    }
    Ok(layout)
  }

  /// Lays out an untagged union of values.
  fn union(&self, variants: &[LayoutId]) -> Layout {
    let size = self.max_size(variants);
    if variants.iter().all(|&v| self.layouts.layouts[v].is_plain()) {
      Layout::data(size)
    } else {
      Layout { size, fields: vec![Field::Opaque { offset: 0, what: "an untagged union" }] }
    }
  }

  fn max_size(&self, layouts: &[LayoutId]) -> u32 {
    layouts.iter().map(|&id| self.layouts.layouts[id].size).max().unwrap_or(0)
  }

  fn opaque_layout(&self, id: OpaqueTypeId) -> Layout {
    let b = &self.chart.builtins;
    if [b.n32, b.i32, b.f32, b.f64, b.char, b.bool, b.io].contains(&Some(id)) {
      Layout::data(1)
    } else if Some(id) == b.hole {
      opaque("a hole")
    } else {
      opaque("an opaque value")
    }
  }

  fn infinite_size(&mut self, Term(kind, _): &Term) -> ErrorGuaranteed {
    let (span, def) = match kind {
      LayoutKind::Struct(id) => (self.chart.structs[*id].span, self.chart.structs[*id].def),
      LayoutKind::Enum(id) => (self.chart.enums[*id].span, self.chart.enums[*id].def),
      LayoutKind::Union(id) => (self.chart.unions[*id].span, self.chart.unions[*id].def),
      // Only nominal types can be recursive.
      _ => unreachable!(),
    };
    if let Some(&err) = self.infinite.get(&def) {
      return err;
    }
    let ty = self.chart.defs[def].path.clone();
    let err = self.diags.error(Diag::InfiniteSize { span, ty });
    self.infinite.insert(def, err);
    err
  }
}

fn opaque(what: &'static str) -> Layout {
  Layout { size: 1, fields: vec![Field::Opaque { offset: 0, what }] }
}
