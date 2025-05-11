use std::collections::HashMap;

use anyhow::{anyhow, bail, Context, Ok, Result};

use crate::ast::{Net, Nets, PrimitiveType, Tree, TreeNode, Type};

pub struct TypeChecker<'a> {
  nets: &'a Nets,
  var_types: HashMap<String, Type>,
}

impl Type {
  pub fn can_interact_with(&self, other: &Self) -> Result<()> {
    match (self, other) {
      (Type::In(ty1), Type::Out(ty2)) | (Type::Out(ty1), Type::In(ty2)) => {
        if ty1 != ty2 {
          bail!("Types {ty1} and {ty2} cannot interact");
        }
        Ok(())
      }
      (Type::In(_), Type::In(_)) | (Type::Out(_), Type::Out(_)) => {
        bail!("Types {self} and {other} of the same polarity cannot interact");
      }
      (
        Type::Pair { label: label1, left: left1, right: right1 },
        Type::Pair { label: label2, left: left2, right: right2 },
      ) => {
        if label1 == label2 {
          left1
            .can_interact_with(left2)
            .context(format!("Left children of: {self} and {other}"))?;

          right1
            .can_interact_with(right2)
            .context(format!("Right children of: {self} and {other}"))?;
        } else {
          left1.can_interact_with(other).context(format!("Left child of {self} and {other}"))?;
          right1.can_interact_with(other).context(format!("Right child of {self} and {other}"))?;
          left2.can_interact_with(self).context(format!("{self} and left child of {other}"))?;
          right2.can_interact_with(self).context(format!("{self} and right child of {other}"))?;
        }
        Ok(())
      }
      (Type::Pair { label: _, left, right }, _) => {
        left.can_interact_with(other).context(format!("Left child of {self} and {other}"))?;
        right.can_interact_with(other).context(format!("Right child of {self} and {other}"))
      }
      (_, Type::Pair { label: _, left, right }) => {
        self.can_interact_with(left).context(format!("{self} and left child of {other}"))?;
        self.can_interact_with(right).context(format!("{self} and right child of {other}"))
      }
    }
  }

  pub fn compatible_with(&self, other: &Type) -> Result<()> {
    match (self, other) {
      (Type::In(ty1), Type::In(ty2)) => {
        if ty1 != ty2 {
          bail!("Types {ty1} and {ty2} are not the same");
        }
        Ok(())
      }
      (Type::Out(ty1), Type::Out(ty2)) => {
        if ty1 != ty2 {
          bail!("Types {ty1} and {ty2} are not the same");
        }
        Ok(())
      }
      (
        Type::Pair { label: label1, left: left1, right: right1 },
        Type::Pair { label: label2, left: left2, right: right2 },
      ) => {
        if label1 != label2 {
          bail!("Types {label1} and {label2} are not the same");
        }
        left1.compatible_with(left2).context(format!("Left children of: {self} and {other}"))?;
        right1.compatible_with(right2).context(format!("Right children of: {self} and {other}"))
      }
      (Type::Pair { label: _, left, right }, prim_ty)
      | (prim_ty, Type::Pair { label: _, left, right }) => {
        left
          .compatible_with(prim_ty)
          .context(format!("Left child of {self} if not compatible with {prim_ty}",))?;
        right
          .compatible_with(prim_ty)
          .context(format!("Right child of {self} if not compatible with {prim_ty}"))
      }
      _ => {
        bail!("Types {self} and {other} are not compatible")
      }
    }
  }
}

impl Tree {
  pub fn can_interact_with(&self, other: &Self) -> Result<()> {
    match (&self.ty, &other.ty) {
      (Some(ty), Some(other_ty)) => ty.can_interact_with(other_ty),
      _ => bail!("Type is empty for {self} or {other}"),
    }
  }
}

impl<'a> TypeChecker<'a> {
  pub fn type_check_nets(&mut self) -> Result<()> {
    for (name, net) in self.nets.iter() {
      self.type_check_net(net).context(format!("Failed to type check net {name}"))?;
    }
    let main_ty = self.nets["::main"].net_type.to_type();
    main_ty
      .compatible_with(&Type::In(PrimitiveType::IO))
      .context(format!("Main net needs to be able to interact with ~IO but has type {main_ty}"))
  }

  fn type_check_net(&mut self, net: &Net) -> Result<()> {
    self.var_types.clear();
    self.type_check_tree(&net.root)?;
    // Check that the root type actually matches the type of the net.
    let net_type = net.net_type.to_type();
    let root_type = net.root.ty.to_owned().unwrap();
    if root_type != net_type {
      bail!("Root of the net has type {root_type} but needs to be {net_type}");
    }
    for (t1, t2) in &net.pairs {
      self.type_check_tree(t1)?;
      self.type_check_tree(t2)?;
      t1.can_interact_with(t2).context(format!("Types of {t1} and {t2} cannot interact"))?;
    }
    Ok(())
  }

  fn type_check_tree(&mut self, tree: &Tree) -> Result<()> {
    if tree.ty.is_none() {
      bail!("Type not set for {tree}");
    }
    let ty = tree.ty.to_owned().unwrap();

    match &tree.tree_node {
      TreeNode::Erase => {}
      TreeNode::N32(_) => match ty {
        Type::Out(PrimitiveType::N32) => {}
        _ => bail!("N32 nodes needs to be of type N32 but got {ty}"),
      },
      TreeNode::F32(_) => match ty {
        Type::Out(PrimitiveType::F32) => {}
        _ => bail!("F32 nodes needs to be of type F32 but got {ty}"),
      },
      TreeNode::Var(name) => match self.var_types.get(name) {
        Some(var_type) => {
          var_type.can_interact_with(&ty).context(format!(
            "Variable {name} has two types that cannot interact: {var_type} and {ty}"
          ))?;
        }
        None => {
          self.var_types.insert(name.to_owned(), ty.to_owned());
        }
      },
      TreeNode::Global(name) => {
        let net_type = self.nets[name].net_type.to_type();
        if net_type != ty {
          bail!("Global {name} has type {net_type} and was used as {ty}");
        }
      }
      TreeNode::ExtFn(name, swapped_arguments, left, right) => {
        let left_ty =
          left.ty.to_owned().ok_or(anyhow!("Left child of {tree} has to have a type"))?;
        let out_ty = right.ty.to_owned().ok_or(anyhow!("Out port of {tree} has no type"))?;
        match name.as_str() {
          "n32_add" | "n32_sub" | "n32_mul" | "n32_div" | "n32_rem" | "n32_eq" | "n32_ne"
          | "n32_lt" | "n32_le" | "n32_shl" | "n32_shr" | "n32_rotl" | "n32_rotr" | "n32_and"
          | "n32_or" | "n32_xor" | "n32_add_high" | "n32_mul_high" => {
            ty.compatible_with(&Type::In(PrimitiveType::N32)).context(format!(
              "Type of ExtFn {name} needs to be compatible with ~N32 but got {ty}"
            ))?;
            left_ty.compatible_with(&Type::Out(PrimitiveType::N32)).context(format!(
              "Left child of ExtFn {name} needs to be compatible with N32 but got {left_ty}"
            ))?;
            out_ty.compatible_with(&Type::In(PrimitiveType::N32)).context(format!(
              "Result port of ExtFn {name} has to be compatible with ~N32 but has type {out_ty}"
            ))?;
          }
          "f32_add" | "f32_sub" | "f32_mul" | "f32_div" | "f32_rem" => {
            ty.compatible_with(&Type::In(PrimitiveType::F32)).context(format!(
              "Type of ExtFn {name} needs to be compatible with ~F32 but got {ty}"
            ))?;
            left_ty.compatible_with(&Type::Out(PrimitiveType::F32)).context(format!(
              "Left child of ExtFn {name} needs to be compatible with F32 but got {left_ty}"
            ))?;
            out_ty.compatible_with(&Type::In(PrimitiveType::F32)).context(format!(
              "Result port of ExtFn {name} has to be compatible with ~F32 but has type {out_ty}"
            ))?;
          }
          "f32_eq" | "f32_ne" | "f32_lt" | "f32_le" => {
            ty.compatible_with(&Type::In(PrimitiveType::N32)).context(format!(
              "Type of ExtFn {name} needs to be compatible with ~N32 but got {ty}"
            ))?;
            left_ty.compatible_with(&Type::Out(PrimitiveType::F32)).context(format!(
              "Left child of ExtFn {name} needs to be compatible with F32 but got {left_ty}"
            ))?;
            out_ty.compatible_with(&Type::In(PrimitiveType::N32)).context(format!(
              "Result port of ExtFn {name} has to be compatible with ~N32 but has type {out_ty}"
            ))?;
          }
          "io_print_char" | "io_print_byte" | "io_flush" | "io_read_byte" => {
            if *swapped_arguments {
              ty.compatible_with(&Type::In(PrimitiveType::N32)).context(format!(
                "ExtFn {name} with swapped arguments needs to be compatible with ~N32 but got {ty}"
              ))?;
              left_ty.compatible_with(&Type::Out(PrimitiveType::IO)).context(format!(
                "Second argument to ExtFn {name} has to be compatible with IO but got {left_ty}"
              ))?;
            } else {
              ty.compatible_with(&Type::In(PrimitiveType::IO))
                .context(format!("ExtFn {name} needs to be compatible with ~IO but got {ty}"))?;
              left_ty.compatible_with(&Type::Out(PrimitiveType::N32)).context(format!(
                "First argument to ExtFn {name} has to be compatible with N32 but got {left_ty}"
              ))?;
            }
            if name == "io_read_byte" {
              out_ty.compatible_with(&Type::In(PrimitiveType::N32)).context(format!(
                "Result port of ExtFn {name} has to be compatible with ~N32 but has type {out_ty}"
              ))?;
            } else {
              out_ty.compatible_with(&Type::In(PrimitiveType::IO)).context(format!(
                "Result port of ExtFn {name} has to be compatible with ~IO but has type {out_ty}"
              ))?;
            }
          }
          "seq" => {
            if *swapped_arguments {
              out_ty.can_interact_with(&left_ty).context(format!("Out port of ExtFn {name} with swapped arguments needs to be able to interact with {left_ty} but has type {out_ty}"))?;
            } else if out_ty != ty {
              bail!("Type of ExtFn {name} needs to be {out_ty} but got {ty}");
            }
          }
          _ => bail!("Cannot type check unknown ExtFn {name}"),
        }
      }
      TreeNode::Comb(label, left_node, right_node) => {
        let left_ty = left_node.ty.to_owned().ok_or(anyhow!("Left child of {tree} has no type"))?;
        let right_ty = right_node.ty.to_owned().ok_or(anyhow!("Right child has no type"))?;
        match ty {
          Type::Pair { label: label_ty, left: l, right: r } => {
            if *label != label_ty {
              bail!("Type label of {tree} needs to be {label_ty} but got {label}");
            }
            if *l != left_ty {
              bail!("Left child of {tree} needs to be of type {l} but got {left_ty}");
            }
            if *r != right_ty {
              bail!("Right child of {tree} needs to be of type {r} but got {right_ty}");
            }
          }
          _ => bail!("Comb nodes needs to be of type Pair but got {ty}"),
        }
      }
      TreeNode::Branch(zero, positive, out) => {
        ty.compatible_with(&Type::In(PrimitiveType::N32))
          .context(format!("Type of {tree} needs to be compatible with ~N32 but got {ty}"))?;
        let zero_ty = zero.ty.to_owned().ok_or(anyhow!("Zero child of {tree} has no type"))?;
        let positive_ty =
          positive.ty.to_owned().ok_or(anyhow!("Positive child of {tree} has no type"))?;
        let out_ty = out.ty.to_owned().ok_or(anyhow!("Out child of {tree} has no type"))?;
        out_ty.can_interact_with(&positive_ty).context(format!("Out child of {tree} needs to be able to interact with {positive_ty} but has type {out_ty}"))?;
        out_ty.can_interact_with(&zero_ty).context(format!(
          "Out child of {tree} needs to be able to interact with {zero_ty} but has type {out_ty}"
        ))?;
      }
      TreeNode::BlackBox(t) => {
        let inner_ty = t.ty.to_owned().ok_or(anyhow!("Inner child of {tree} has no type"))?;
        if ty != inner_ty {
          bail!("BlackBox nodes needs to be of type {inner_ty} but got {ty}");
        }
      }
    };

    for child in tree.children() {
      self.type_check_tree(child)?;
    }

    Ok(())
  }
}

impl<'a> TypeChecker<'a> {
  pub fn type_check(nets: &Nets) -> Result<()> {
    let mut type_checker = TypeChecker { nets, var_types: HashMap::new() };
    type_checker.type_check_nets()
  }
}
