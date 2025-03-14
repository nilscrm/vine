use std::collections::HashMap;

use crate::ast::{Nets, Polarity, PrimitiveType, Tree, TreeNode, Type};

pub struct TypeInference {
  global_types: HashMap<String, Option<Type>>,
}

impl TypeInference {
  pub fn infer_types_nets(&mut self, nets: &mut Nets) {
    for net in nets.values_mut() {
      for tree in net.trees_mut() {
        self.infer_types_tree(tree, tree.ty.to_owned().as_ref());
      }
    }
  }

  fn infer_types_tree(&self, tree: &mut Tree, hint: Option<&Type>) {
    let inferred_type = match &mut tree.tree_node {
      TreeNode::Erase => None,
      TreeNode::N32(_) => {
        Some(Type::Primitive { ty: PrimitiveType::N32, polarity: Polarity::Out, lifetime: None })
      }
      TreeNode::F32(_) => {
        Some(Type::Primitive { ty: PrimitiveType::F32, polarity: Polarity::Out, lifetime: None })
      }
      TreeNode::Var(_) => None,
      TreeNode::Global(name) => self.global_types[name].to_owned(),
      TreeNode::ExtFn(name, swapped_arguments, left, right) => {
        self.infer_types_tree(left, None);
        self.infer_types_tree(right, None);
        match name.as_str() {
          "n32_add" | "n32_sub" | "n32_mul" | "n32_div" | "n32_rem" | "n32_eq" | "n32_ne"
          | "n32_lt" | "n32_le" => {
            Some(Type::Primitive { ty: PrimitiveType::N32, polarity: Polarity::In, lifetime: None })
          }
          "f32_add" | "f32_sub" | "f32_mul" | "f32_div" | "f32_rem" | "f32_eq" | "f32_ne"
          | "f32_lt" | "f32_le" => {
            Some(Type::Primitive { ty: PrimitiveType::F32, polarity: Polarity::In, lifetime: None })
          }
          "n32_shl" | "n32_shr" | "n32_rotl" | "n32_rotr" | "n32_and" | "n32_or" | "n32_xor"
          | "n32_add_high" | "n32_mul_high" => {
            Some(Type::Primitive { ty: PrimitiveType::N32, polarity: Polarity::In, lifetime: None })
          }
          "io_print_char" | "io_print_byte" | "io_flush" | "io_read_byte" => {
            if *swapped_arguments {
              Some(Type::Primitive {
                ty: PrimitiveType::N32,
                polarity: Polarity::In,
                lifetime: None,
              })
            } else {
              Some(Type::Primitive {
                ty: PrimitiveType::IO,
                polarity: Polarity::In,
                lifetime: None,
              })
            }
          }
          "seq" => right.ty.to_owned(),
          _ => None,
        }
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
        Some(Type::Primitive { ty: PrimitiveType::N32, polarity: Polarity::In, lifetime: None })
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
      nets.iter().map(|(name, net)| (name.to_owned(), net.ty().to_owned())).collect();
    let mut type_inference = TypeInference { global_types };
    type_inference.infer_types_nets(nets);
  }
}
