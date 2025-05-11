use std::{
  fmt::{self, Display},
  iter,
  ops::{Deref, DerefMut},
};

use indexmap::IndexMap;

use vine_util::multi_iter;

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum PrimitiveType {
  N32,
  F32,
  IO,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FlowLabel {
  Default,
  Label(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum NetType {
  In { ty: PrimitiveType, flow_label: FlowLabel },
  Out { ty: PrimitiveType, flow_labels: Vec<FlowLabel> },
  Pair { label: String, left: Box<NetType>, right: Box<NetType> },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
  In(PrimitiveType),
  Out(PrimitiveType),
  Pair { label: String, left: Box<Type>, right: Box<Type> },
}

#[derive(Default, Debug, Clone, PartialEq)]
pub enum TreeNode {
  #[default]
  Erase,
  Comb(String, Box<Tree>, Box<Tree>),
  ExtFn(String, bool, Box<Tree>, Box<Tree>),
  Branch(Box<Tree>, Box<Tree>, Box<Tree>),
  N32(u32),
  F32(f32),
  Var(String),
  Global(String),
  BlackBox(Box<Tree>),
}

#[derive(Default, Debug, Clone, PartialEq)]
pub struct Tree {
  pub ty: Option<Type>,
  pub tree_node: TreeNode,
}

#[derive(Debug, Clone)]
pub struct Net {
  pub net_type: NetType,
  pub root: Tree,
  pub pairs: Vec<(Tree, Tree)>,
}

#[derive(Debug, Default, Clone)]
pub struct Nets(IndexMap<String, Net>);

impl NetType {
  pub fn to_type(&self) -> Type {
    match self {
      NetType::In { ty, .. } => Type::In(*ty),
      NetType::Out { ty, .. } => Type::Out(*ty),
      NetType::Pair { label, left, right } => Type::Pair {
        label: label.clone(),
        left: Box::new(left.to_type()),
        right: Box::new(right.to_type()),
      },
    }
  }
}

impl Net {
  pub fn trees(&self) -> impl DoubleEndedIterator<Item = &Tree> + Clone {
    iter::once(&self.root).chain(self.pairs.iter().flat_map(|(a, b)| [a, b]))
  }
  pub fn trees_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Tree> {
    iter::once(&mut self.root).chain(self.pairs.iter_mut().flat_map(|(a, b)| [a, b]))
  }
}

impl Tree {
  pub fn children(&self) -> impl DoubleEndedIterator + ExactSizeIterator<Item = &Self> + Clone {
    multi_iter!(Children { Zero, One, Two, Three });
    match &self.tree_node {
      TreeNode::Erase
      | TreeNode::N32(_)
      | TreeNode::F32(_)
      | TreeNode::Var(_)
      | TreeNode::Global(_) => Children::Zero([]),
      TreeNode::Comb(_, a, b) | TreeNode::ExtFn(_, _, a, b) => Children::Two([&**a, b]),
      TreeNode::Branch(a, b, c) => Children::Three([&**a, b, c]),
      TreeNode::BlackBox(a) => Children::One([&**a]),
    }
  }

  pub fn children_mut(&mut self) -> impl DoubleEndedIterator + ExactSizeIterator<Item = &mut Self> {
    multi_iter!(Children { Zero, One, Two, Three });
    match &mut self.tree_node {
      TreeNode::Erase
      | TreeNode::N32(_)
      | TreeNode::F32(_)
      | TreeNode::Var(_)
      | TreeNode::Global(_) => Children::Zero([]),
      TreeNode::Comb(_, a, b) | TreeNode::ExtFn(_, _, a, b) => Children::Two([&mut **a, b]),
      TreeNode::Branch(a, b, c) => Children::Three([&mut **a, b, c]),
      TreeNode::BlackBox(a) => Children::One([&mut **a]),
    }
  }

  pub fn n_ary(
    label: &str,
    ports: impl IntoIterator<IntoIter: DoubleEndedIterator<Item = Tree>>,
  ) -> Self {
    ports
      .into_iter()
      .rev()
      .reduce(|b, a| match (&b.ty, &a.ty) {
        (Some(a_ty), Some(b_ty)) => Tree {
          ty: Some(Type::Pair {
            label: label.into(),
            left: Box::new(a_ty.to_owned()),
            right: Box::new(b_ty.to_owned()),
          }),
          tree_node: TreeNode::Comb(label.into(), Box::new(a), Box::new(b)),
        },
        _ => Tree { ty: None, tree_node: TreeNode::Comb(label.into(), Box::new(a), Box::new(b)) },
      })
      .unwrap_or_default()
  }
}

impl Deref for Nets {
  type Target = IndexMap<String, Net>;
  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

impl DerefMut for Nets {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut self.0
  }
}

impl Display for PrimitiveType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      PrimitiveType::N32 => write!(f, "N32"),
      PrimitiveType::F32 => write!(f, "F32"),
      PrimitiveType::IO => write!(f, "IO"),
    }
  }
}

impl Display for FlowLabel {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      FlowLabel::Default => write!(f, ""),
      FlowLabel::Label(label) => write!(f, "'{label}"),
    }
  }
}

impl Display for NetType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      NetType::In { ty, flow_label: flow } => write!(f, "~{ty}{flow}"),
      NetType::Out { ty, flow_labels: flow } => {
        write!(f, "{ty}")?;
        for flow in flow {
          write!(f, "{flow}")?;
        }
        Ok(())
      }
      NetType::Pair { label, left, right } => write!(f, "{label}({left} {right})"),
    }
  }
}

impl Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Type::In(ty) => write!(f, "~{ty}"),
      Type::Out(ty) => write!(f, "{ty}"),
      Type::Pair { label, left, right } => write!(f, "{label}({left} {right})"),
    }
  }
}

impl Display for TreeNode {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      TreeNode::Erase => write!(f, "_"),
      TreeNode::Comb(n, a, b) => write!(f, "{n}({a} {b})"),
      TreeNode::ExtFn(e, swap, a, b) => write!(f, "@{e}{}({a} {b})", if *swap { "$" } else { "" }),
      TreeNode::Branch(a, b, c) => write!(f, "?({a} {b} {c})"),
      TreeNode::N32(n) => write!(f, "{n}"),
      TreeNode::F32(n) if n.is_nan() => write!(f, "+NaN"),
      TreeNode::F32(n) => write!(f, "{n:+?}"),
      TreeNode::Var(v) => write!(f, "{v}"),
      TreeNode::Global(g) => write!(f, "{g}"),
      TreeNode::BlackBox(b) => write!(f, "#[{b}]"),
    }
  }
}

impl Display for Tree {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if let Some(ty) = &self.ty {
      write!(f, "{}:{}", self.tree_node, ty)
    } else {
      write!(f, "{}", self.tree_node)
    }
  }
}

impl Display for Net {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if self.pairs.is_empty() {
      write!(f, "{{ {} }}", self.root)?;
    } else {
      write!(f, "{{\n  {}", self.root)?;
      for (a, b) in &self.pairs {
        write!(f, "\n  {a} = {b}")?;
      }
      write!(f, "\n}}")?;
    }
    Ok(())
  }
}

impl Display for Nets {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for (name, net) in self.iter() {
      write!(f, "\n{name} {net}\n")?;
    }
    Ok(())
  }
}
