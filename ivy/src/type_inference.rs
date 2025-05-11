use std::collections::HashMap;

use crate::ast::{NetType, Nets, PrimitiveType, Tree, TreeNode, Type};

pub struct TypeInference {
  global_types: HashMap<String, NetType>,
}

impl TypeInference {
  pub fn infer_types_nets(&mut self, nets: &mut Nets) {
    for net in nets.values_mut() {
      let net_type = net.net_type.to_type();
      self.infer_types_tree(&mut net.root, Some(&net_type));
      for (t1, t2) in &mut net.pairs {
        self.infer_types_tree(t1, None);
        self.infer_types_tree(t2, None);
      }
    }
  }

  fn infer_types_tree(&self, tree: &mut Tree, hint: Option<&Type>) {
    let hint = hint.or(tree.ty.as_ref());
    let inferred_type = match &mut tree.tree_node {
      TreeNode::Erase => None,
      TreeNode::N32(_) => Some(Type::Out(PrimitiveType::N32)),
      TreeNode::F32(_) => Some(Type::Out(PrimitiveType::F32)),
      TreeNode::Var(_) => None,
      TreeNode::Global(name) => Some(self.global_types[name].to_type()),
      TreeNode::ExtFn(name, swapped_arguments, left, right) => {
        let mut hint_left = None;
        let mut hint_right = None;
        let inferred_type = match name.as_str() {
          "n32_add" | "n32_sub" | "n32_mul" | "n32_div" | "n32_rem" | "n32_eq" | "n32_ne"
          | "n32_lt" | "n32_le" | "n32_shl" | "n32_shr" | "n32_rotl" | "n32_rotr" | "n32_and"
          | "n32_or" | "n32_xor" | "n32_add_high" | "n32_mul_high" => {
            hint_left = Some(Type::Out(PrimitiveType::N32));
            hint_right = Some(Type::In(PrimitiveType::N32));
            Some(Type::In(PrimitiveType::N32))
          }
          "f32_add" | "f32_sub" | "f32_mul" | "f32_div" | "f32_rem" | "f32_eq" | "f32_ne"
          | "f32_lt" | "f32_le" => {
            hint_left = Some(Type::Out(PrimitiveType::F32));
            hint_right = Some(Type::In(PrimitiveType::F32));
            Some(Type::In(PrimitiveType::F32))
          }
          "io_print_char" | "io_print_byte" | "io_flush" | "io_read_byte" => {
            if name.as_str() == "io_read_byte" {
              hint_right = Some(Type::In(PrimitiveType::N32));
            } else {
              hint_right = Some(Type::In(PrimitiveType::IO));
            }
            if *swapped_arguments {
              hint_left = Some(Type::Out(PrimitiveType::IO));
              Some(Type::In(PrimitiveType::N32))
            } else {
              hint_left = Some(Type::Out(PrimitiveType::N32));
              Some(Type::In(PrimitiveType::IO))
            }
          }
          "seq" => right.ty.to_owned(),
          _ => None,
        };
        self.infer_types_tree(left, hint_left.as_ref());
        self.infer_types_tree(right, hint_right.as_ref());
        inferred_type
      }
      TreeNode::Comb(label, left_node, right_node) => {
        let (left_hint, right_hint) =
          if let Some(Type::Pair { label: _, left, right }) = hint.or(tree.ty.as_ref()) {
            (Some(left.as_ref()), Some(right.as_ref()))
          } else {
            (None, None)
          };
        self.infer_types_tree(left_node, left_hint);
        self.infer_types_tree(right_node, right_hint);
        match (&left_node.ty, &right_node.ty) {
          (Some(left_ty), Some(right_ty)) => Some(Type::Pair {
            label: label.to_owned(),
            left: Box::new(left_ty.to_owned()),
            right: Box::new(right_ty.to_owned()),
          }),
          _ => None,
        }
      }
      TreeNode::Branch(zero, positive, out) => {
        self.infer_types_tree(zero, None);
        self.infer_types_tree(positive, None);
        self.infer_types_tree(out, None);
        Some(Type::In(PrimitiveType::N32))
      }
      TreeNode::BlackBox(inner) => {
        self.infer_types_tree(inner, hint);
        inner.ty.to_owned()
      }
    };

    if tree.ty.is_none() {
      if inferred_type.is_some() {
        tree.ty = inferred_type;
      } else {
        tree.ty = hint.cloned();
      }
    }
  }
}

impl TypeInference {
  pub fn infer_types(nets: &mut Nets) {
    let global_types =
      nets.iter().map(|(name, net)| (name.to_owned(), net.net_type.to_owned())).collect();
    let mut type_inference = TypeInference { global_types };
    type_inference.infer_types_nets(nets);
  }
}
