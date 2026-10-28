//! Computes the concrete layouts of values, as used by the frames runtime.

use std::{collections::HashMap, fmt::Write};

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

/// How a value is stored.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Layout {
  /// The number of words the value occupies.
  pub size: u32,
  /// Whether the value is plain data, i.e. contains no pointers, spaces, or
  /// other handles; such a value can be copied by copying its words, and
  /// dropped by doing nothing.
  pub plain: bool,
}

impl Layout {
  const EMPTY: Layout = Layout { size: 0, plain: true };
  const HANDLE: Layout = Layout { size: 1, plain: false };
}

#[derive(Debug, Clone, Copy)]
enum State {
  /// Its layout is being computed; encountering it again means that it has
  /// infinite size.
  InProgress,
  Done(Result<Layout, ErrorGuaranteed>),
}

pub struct Layouter<'a> {
  chart: &'a Chart,
  sigs: &'a Signatures,
  specs: &'a Specializations,
  pub diags: &'a mut Diags,
  states: HashMap<Term, State>,
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
    Layouter { chart, sigs, specs, diags, states: HashMap::new(), infinite: HashMap::new() }
  }

  /// Returns the layout described by an implementation of `Layout`.
  pub fn impl_tree_layout(&mut self, tree: ImplTreeId) -> Result<Layout, ErrorGuaranteed> {
    let term = self.impl_tree_term(tree)?;
    self.term_layout(term)
  }

  /// Returns the layout of a type, given the layouts of its type parameters.
  pub fn type_layout(
    &mut self,
    types: &Types,
    ty: Type,
    params: &[Term],
  ) -> Result<Layout, ErrorGuaranteed> {
    let term = self.type_term(types, ty, params)?;
    self.term_layout(term)
  }

  /// The layouts of the variants of an enum type.
  pub fn variant_layouts_of(
    &mut self,
    types: &Types,
    ty: Type,
    params: &[Term],
  ) -> Result<Vec<Layout>, ErrorGuaranteed> {
    let Term(LayoutKind::Enum(id), children) = self.type_term(types, ty, params)? else {
      unreachable!("expected an enum")
    };
    let sig = &self.sigs.enums[id];
    self.variant_layouts(&sig.types, sig.inner.variant_data.values(), &children)
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

  pub fn term_layout(&mut self, term: Term) -> Result<Layout, ErrorGuaranteed> {
    match self.states.get(&term) {
      Some(State::Done(result)) => *result,
      Some(State::InProgress) => Err(self.infinite_size(&term)),
      None => {
        self.states.insert(term.clone(), State::InProgress);
        let result = self.compute(&term);
        self.states.insert(term, State::Done(result));
        result
      }
    }
  }

  fn compute(&mut self, Term(kind, children): &Term) -> Result<Layout, ErrorGuaranteed> {
    let sigs = self.sigs;
    Ok(match kind {
      LayoutKind::Empty => Layout::EMPTY,
      LayoutKind::Space | LayoutKind::Closure => Layout::HANDLE,
      LayoutKind::Composite => self.concat(children)?,
      LayoutKind::Ref => {
        let value = self.concat(children)?;
        Layout { size: value.size + 1, plain: false }
      }
      LayoutKind::Opaque(id) => self.opaque_layout(*id)?,
      // The contents of a box do not affect its layout.
      LayoutKind::Struct(id) if Some(*id) == self.chart.builtins.box_ => Layout::HANDLE,
      LayoutKind::Struct(id) => {
        let sig = &sigs.structs[*id];
        let term = self.type_term(&sig.types, sig.inner.data, children)?;
        self.term_layout(term)?
      }
      LayoutKind::Enum(id) => {
        let sig = &sigs.enums[*id];
        let variants =
          self.variant_layouts(&sig.types, sig.inner.variant_data.values(), children)?;
        let union = union(&variants);
        Layout { size: 1 + union.size, plain: union.plain }
      }
      LayoutKind::Union(id) => {
        let sig = &sigs.unions[*id];
        union(&self.variant_layouts(&sig.types, sig.inner.variant_data.values(), children)?)
      }
      // The frames runtime has no debug mode.
      LayoutKind::IfConst(id)
        if Some(self.chart.concrete_consts[*id].def) == self.chart.builtins.debug_enabled =>
      {
        self.term_layout(children[1].clone())?
      }
      LayoutKind::IfConst(_) => {
        let branches = children
          .iter()
          .map(|child| self.term_layout(child.clone()))
          .collect::<Result<Vec<_>, _>>()?;
        union(&branches)
      }
    })
  }

  fn variant_layouts<'t>(
    &mut self,
    types: &Types,
    variants: impl IntoIterator<Item = &'t Type>,
    children: &[Term],
  ) -> Result<Vec<Layout>, ErrorGuaranteed> {
    variants
      .into_iter()
      .map(|&ty| {
        let term = self.type_term(types, ty, children)?;
        self.term_layout(term)
      })
      .collect()
  }

  /// Lays out values one after another.
  fn concat(&mut self, terms: &[Term]) -> Result<Layout, ErrorGuaranteed> {
    let mut layout = Layout::EMPTY;
    for term in terms {
      let part = self.term_layout(term.clone())?;
      layout.size += part.size;
      layout.plain &= part.plain;
    }
    Ok(layout)
  }

  /// A `Frame` is a handle (a pointer to the frame); other opaque types are
  /// plain data of their declared size.
  fn opaque_layout(&mut self, id: OpaqueTypeId) -> Result<Layout, ErrorGuaranteed> {
    if Some(id) == self.chart.builtins.frame {
      return Ok(Layout::HANDLE);
    }
    let opaque = &self.chart.opaque_types[id];
    match opaque.size {
      Some(size) => Ok(Layout { size, plain: true }),
      None => {
        let ty = self.chart.defs[opaque.def].path.clone();
        Err(self.diags.error(Diag::MissingOpaqueSize { span: opaque.span, ty }))
      }
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

  /// Renders a term as the type it describes, as far as is possible.
  pub fn show_term(&self, Term(kind, children): &Term) -> String {
    let mut children = children.iter().map(|child| self.show_term(child));
    let def = match kind {
      LayoutKind::Empty => return "()".into(),
      LayoutKind::Space => return "~_".into(),
      LayoutKind::Closure => return "fn _".into(),
      LayoutKind::Ref => return format!("&{}", children.next().unwrap()),
      LayoutKind::Composite => return format!("({})", children.collect::<Vec<_>>().join(", ")),
      LayoutKind::Struct(id) => self.chart.structs[*id].def,
      LayoutKind::Enum(id) => self.chart.enums[*id].def,
      LayoutKind::Union(id) => self.chart.unions[*id].def,
      LayoutKind::Opaque(id) => self.chart.opaque_types[*id].def,
      LayoutKind::IfConst(id) => self.chart.concrete_consts[*id].def,
    };
    let mut str = self.chart.defs[def].path.clone();
    let children = children.collect::<Vec<_>>();
    if !children.is_empty() {
      write!(str, "[{}]", children.join(", ")).unwrap();
    }
    str
  }
}

/// Lays out an untagged union of values.
fn union(variants: &[Layout]) -> Layout {
  Layout {
    size: variants.iter().map(|v| v.size).max().unwrap_or(0),
    plain: variants.iter().all(|v| v.plain),
  }
}
