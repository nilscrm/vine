use std::{
  collections::{hash_map::Entry, HashMap},
  mem::take,
};

use crate::ast::{Net, Tree, TreeNode};

#[derive(Debug, Default)]
pub(super) struct InlineVars {
  mappings: HashMap<String, Tree>,
}

impl InlineVars {
  //! Remove all `var = tree` pairs, inlining the `tree` into the usage of
  //! `var`.
  pub fn apply(&mut self, net: &mut Net) {
    net.pairs.retain_mut(|pair| loop {
      match pair {
        (Tree { ty: _, tree_node: TreeNode::Var(v) }, t)
        | (t, Tree { ty: _, tree_node: TreeNode::Var(v) }) => {
          let v = take(v);
          let t = take(t);
          match self.mappings.entry(v) {
            Entry::Vacant(e) => {
              e.insert(t);
              break false;
            }
            Entry::Occupied(e) => *pair = (e.remove(), t),
          }
        }
        (
          Tree { ty: _, tree_node: TreeNode::Erase },
          Tree { ty: _, tree_node: TreeNode::Erase },
        ) => break false,
        _ => break true,
      }
    });

    for tree in net.trees_mut() {
      self.apply_tree(tree);
    }

    debug_assert!(self.mappings.is_empty());
  }

  fn apply_tree(&mut self, tree: &mut Tree) {
    while let TreeNode::Var(var) = &tree.tree_node {
      let Some(new) = self.mappings.remove(var) else { break };
      *tree = new;
    }

    for child in tree.children_mut() {
      self.apply_tree(child)
    }
  }
}
