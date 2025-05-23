use std::fmt::{self, Display};

use indexmap::{map::Entry, IndexMap};
use ivm::{
  port::{Port, Tag},
  wire::Wire,
  IVM,
};
use vine_util::parser::{Parser, ParserState};

use crate::{
  ast::{Tree, TreeNode},
  host::Host,
  parser::{IvyParser, ParseError},
};

pub struct Repl<'host, 'ctx, 'ivm, 'ext> {
  pub host: &'host mut Host<'ivm>,
  pub ivm: &'ctx mut IVM<'ivm, 'ext>,
  pub vars: IndexMap<String, Port<'ivm>>,
}

impl<'host, 'ctx, 'ivm, 'ext> Repl<'host, 'ctx, 'ivm, 'ext> {
  pub fn new(host: &'host mut Host<'ivm>, ivm: &'ctx mut IVM<'ivm, 'ext>) -> Self {
    let vars = [("io".to_owned(), Port::new_ext_val(host.new_io()))].into_iter().collect();
    Self { host, ivm, vars }
  }

  pub fn exec<'s>(&mut self, line: &'s str) -> Result<(), ParseError<'s>> {
    let mut parser = IvyParser { state: ParserState::new(line) };
    parser.bump()?;
    let mut pairs = Vec::new();
    while parser.state.token.is_some() {
      pairs.push(parser.parse_pair()?);
    }
    for pair in pairs {
      self.exec_pair(pair);
    }
    Ok(())
  }

  pub fn exec_pair(&mut self, pair: (Tree, Tree)) {
    let p = self.inject(pair.0.tree_node);
    let q = self.inject(pair.1.tree_node);
    self.ivm.link(p, q);
    self.ivm.normalize();
  }

  fn inject_to(&mut self, tree: TreeNode, to: Wire<'ivm>) {
    if let TreeNode::Var(v) = tree {
      match self.vars.entry(v) {
        Entry::Occupied(e) => {
          let p = e.shift_remove();
          self.ivm.link_wire(to, p);
        }
        Entry::Vacant(e) => {
          e.insert(Port::new_wire(to));
        }
      }
    } else {
      let p = self.inject(tree);
      self.ivm.link_wire(to, p);
    }
  }

  fn inject(&mut self, tree: TreeNode) -> Port<'ivm> {
    match tree {
      TreeNode::Erase => Port::ERASE,
      TreeNode::N32(value) => Port::new_ext_val(self.host.new_n32(value)),
      TreeNode::F32(value) => Port::new_ext_val(self.host.new_f32(value)),
      TreeNode::Global(name) => Port::new_global(self.host.get(&name).unwrap()),
      TreeNode::Comb(label, a, b) => {
        let label = self.host.label_to_u16(label);
        let n = unsafe { self.ivm.new_node(Tag::Comb, label) };
        self.inject_to(a.tree_node, n.1);
        self.inject_to(b.tree_node, n.2);
        n.0
      }
      TreeNode::ExtFn(f, swap, a, b) => {
        let f = self.host.instantiate_ext_fn(&f, swap);
        let n = unsafe { self.ivm.new_node(Tag::ExtFn, f.bits()) };
        self.inject_to(a.tree_node, n.1);
        self.inject_to(b.tree_node, n.2);
        n.0
      }
      TreeNode::Branch(z, p, o) => {
        let n = unsafe { self.ivm.new_node(Tag::Branch, 0) };
        let m = unsafe { self.ivm.new_node(Tag::Branch, 0) };
        self.ivm.link_wire(n.1, m.0);
        self.inject_to(z.tree_node, m.1);
        self.inject_to(p.tree_node, m.2);
        self.inject_to(o.tree_node, n.2);
        n.0
      }
      TreeNode::Var(v) => match self.vars.entry(v) {
        Entry::Occupied(e) => e.shift_remove(),
        Entry::Vacant(e) => {
          let (a, b) = self.ivm.new_wire();
          e.insert(Port::new_wire(a));
          Port::new_wire(b)
        }
      },
      TreeNode::BlackBox(t) => self.inject(t.tree_node),
    }
  }
}

impl Display for Repl<'_, '_, '_, '_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for (var, port) in &self.vars {
      writeln!(f, "{} = {}", var, self.host.read(self.ivm, port))?;
    }
    Ok(())
  }
}
