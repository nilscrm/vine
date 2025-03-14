use std::collections::HashMap;

use crate::ast::{Net, Nets, Tree, TreeNode};

/// Inline any globals defined to be single-node nets.
pub fn inline_globals(nets: &mut Nets) -> bool {
  let mut inliner = Inliner::default();
  inliner.populate_candidates(nets);
  for (_, net) in nets.iter_mut() {
    for tree in net.trees_mut() {
      inliner.process(tree);
    }
  }
  inliner.inlined
}

#[derive(Debug, Default)]
struct Inliner {
  candidates: HashMap<String, Tree>,
  inlined: bool,
}

impl Inliner {
  fn populate_candidates(&mut self, nets: &Nets) {
    for (name, mut net) in nets.iter() {
      if net.should_inline() {
        while let TreeNode::Global(name) = &net.root.tree_node {
          let referenced = &nets[name];
          if referenced.should_inline() {
            net = referenced;
          } else {
            break;
          }
        }
        self.candidates.insert(name.to_owned(), net.root.clone());
      }
    }
  }

  fn process(&mut self, tree: &mut Tree) {
    if let TreeNode::Global(name) = &mut tree.tree_node {
      if let Some(inlined) = self.candidates.get(name) {
        *tree = inlined.clone();
        self.inlined = true;
      }
    } else {
      for t in tree.children_mut() {
        self.process(t);
      }
    }
  }
}

impl Net {
  fn should_inline(&self) -> bool {
    self.pairs.is_empty() && self.root.is_nilary()
  }
}

impl Tree {
  fn is_nilary(&self) -> bool {
    self.tree_node.is_nilary()
  }
}

impl TreeNode {
  fn is_nilary(&self) -> bool {
    match self {
      TreeNode::Erase | TreeNode::N32(_) | TreeNode::F32(_) | TreeNode::Global(_) => true,
      TreeNode::Comb(..) | TreeNode::ExtFn(..) | TreeNode::Branch(..) | TreeNode::Var(_) => false,
      TreeNode::BlackBox(t) => t.is_nilary(),
    }
  }
}
