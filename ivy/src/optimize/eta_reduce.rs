use std::{
  collections::{hash_map::Entry, HashMap},
  mem::take,
};

use crate::ast::{Net, Tree, TreeNode};

impl Net {
  /// Apply eta-reduction rules to every net; replacing `(_ _)` with `_` and
  /// `(a b) ... (a b)` with `x ... x`.
  pub fn eta_reduce(&mut self) -> bool {
    let mut walker = WalkTrees::default();
    for tree in self.trees() {
      walker.walk_tree(tree);
    }
    let nodes = { walker }.nodes;
    let mut reducer = ReduceTrees { nodes: &nodes, index: 0, reduced: false };
    for tree in self.trees_mut() {
      reducer.reduce_tree(tree);
    }
    reducer.reduced
  }
}

#[derive(Debug, Clone, PartialEq)]
enum NodeKind {
  Comb(String),
  Var(isize),
  N32(u32),
  F32(f32),
  Erase,
  Other,
  Hole,
}

#[derive(Debug, Default)]
struct WalkTrees<'a> {
  vars: HashMap<&'a str, usize>,
  nodes: Vec<NodeKind>,
}

impl<'a> WalkTrees<'a> {
  fn walk_tree(&mut self, tree: &'a Tree) {
    let kind = match &tree.tree_node {
      TreeNode::Erase => NodeKind::Erase,
      TreeNode::N32(n) => NodeKind::N32(*n),
      TreeNode::F32(n) => NodeKind::F32(*n),
      TreeNode::Var(v) => match self.vars.entry(v) {
        Entry::Occupied(e) => {
          let i = e.remove() as isize;
          let j = self.nodes.len() as isize;
          self.nodes[i as usize] = NodeKind::Var(j - i);
          NodeKind::Var(i - j)
        }
        Entry::Vacant(e) => {
          e.insert(self.nodes.len());
          NodeKind::Hole
        }
      },
      TreeNode::Comb(l, ..) => NodeKind::Comb(l.clone()),
      _ => NodeKind::Other,
    };
    self.nodes.push(kind);
    for t in tree.children() {
      self.walk_tree(t)
    }
  }
}

#[derive(Debug)]
struct ReduceTrees<'a> {
  nodes: &'a [NodeKind],
  index: usize,
  reduced: bool,
}

impl<'a> ReduceTrees<'a> {
  fn reduce_tree(&mut self, tree: &mut Tree) -> &'a NodeKind {
    let index = self.index;
    self.index += 1;
    let kind = &self.nodes[index];
    if let TreeNode::Comb(_, a, b) = &mut tree.tree_node {
      let ak = self.reduce_tree(a);
      let bk = self.reduce_tree(b);
      if ak == bk {
        let reducible = match ak {
          NodeKind::Var(delta) => &self.nodes[index.wrapping_add_signed(*delta)] == kind,
          NodeKind::Erase | NodeKind::N32(_) | NodeKind::F32(_) => true,
          _ => false,
        };
        if reducible {
          self.reduced = true;
          *tree = take(a);
          return ak;
        }
      }
    } else {
      for t in tree.children_mut() {
        self.reduce_tree(t);
      }
    }
    kind
  }
}
