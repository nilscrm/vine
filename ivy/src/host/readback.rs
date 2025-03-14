use std::collections::{hash_map::Entry, HashMap};

use ivm::{
  addr::Addr,
  port::{Port, PortRef, Tag},
  wire::Wire,
  IVM,
};

use crate::{
  ast::{Tree, TreeNode},
  host::Host,
};

impl<'ivm> Host<'ivm> {
  pub fn read<'ext>(&self, ivm: &IVM<'ivm, 'ext>, port: &Port<'ivm>) -> Tree {
    Reader::new(ivm, self).read_port(port)
  }

  pub fn reader<'ctx, 'ext>(&'ctx self, ivm: &'ctx IVM<'ivm, 'ext>) -> Reader<'ctx, 'ivm, 'ext> {
    Reader::new(ivm, self)
  }
}

pub struct Reader<'ctx, 'ivm, 'ext> {
  ivm: &'ctx IVM<'ivm, 'ext>,
  host: &'ctx Host<'ivm>,
  vars: HashMap<Addr, usize>,
  next_var: usize,
}

impl<'ctx, 'ivm, 'ext> Reader<'ctx, 'ivm, 'ext> {
  fn new(ivm: &'ctx IVM<'ivm, 'ext>, host: &'ctx Host<'ivm>) -> Self {
    Reader { ivm, host, vars: HashMap::new(), next_var: 0 }
  }

  pub fn read_port(&mut self, p: &Port<'ivm>) -> Tree {
    Tree { ty: None, tree_node: self.read_port_node(p) }
  }

  fn read_port_node(&mut self, p: &Port<'ivm>) -> TreeNode {
    let p = self.ivm.follow_ref(p);
    match p.tag() {
      Tag::Wire => {
        let n = match self.vars.entry(p.addr()) {
          Entry::Occupied(e) => e.remove(),
          Entry::Vacant(e) => {
            let n = self.next_var;
            self.next_var += 1;
            e.insert(n);
            n
          }
        };
        TreeNode::Var(format!("n{n}"))
      }
      Tag::Global => TreeNode::Global(unsafe { p.as_global() }.name.clone()),
      Tag::Erase => TreeNode::Erase,
      Tag::ExtVal => {
        let val = unsafe { p.as_ext_val() };
        let ext_ty_name = self.host.reverse_ext_tys.get(&val.ty()).unwrap();
        match ext_ty_name.as_str() {
          "N32" => TreeNode::N32(val.payload()),
          "F32" => TreeNode::F32(f32::from_bits(val.payload())),
          "IO" => TreeNode::Var("#io".into()),
          name => TreeNode::Var(format!("#{}", name)),
        }
      }
      Tag::Comb => {
        let label = p.label();
        let (p1, p2) = unsafe { p.aux_ref() };
        TreeNode::Comb(
          self.host.label_from_u16(label).to_owned(),
          self.read_wire(&p1),
          self.read_wire(&p2),
        )
      }
      Tag::ExtFn => {
        let mut f = unsafe { p.as_ext_fn() };
        let swapped = f.is_swapped();
        if swapped {
          f = f.swap();
        }
        let f_name = self.host.reverse_ext_fns.get(&f).unwrap();
        let (p1, p2) = unsafe { p.aux_ref() };
        TreeNode::ExtFn(f_name.clone(), swapped, self.read_wire(&p1), self.read_wire(&p2))
      }
      Tag::Branch => {
        let (p1, p2) = unsafe { p.aux_ref() };
        let p1 = PortRef::new_wire(&p1);
        let p1 = self.ivm.follow_ref(&p1);
        assert_eq!(p1.tag(), Tag::Branch);
        let (p11, p12) = unsafe { p1.aux_ref() };
        TreeNode::Branch(self.read_wire(&p11), self.read_wire(&p12), self.read_wire(&p2))
      }
    }
  }

  fn read_wire(&mut self, w: &Wire<'ivm>) -> Box<Tree> {
    Box::new(self.read_port(&PortRef::new_wire(w)))
  }
}
