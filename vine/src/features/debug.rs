use std::{collections::HashMap, mem::replace};

use ivy::{
  name::{FromTable, NameId, Table},
  net::{FlatNet, Wire},
  translate::Translator,
};

use crate::{compiler::Guide, components::emitter::Emitter};

impl Emitter<'_> {
  pub(crate) fn tap_debug(&mut self) -> Wire {
    let dbg_out = self.net.wire();
    let dbg_in = replace(&mut self.debug_state.as_mut().unwrap().0, dbg_out);
    self.net.make(self.guide.ref_, [dbg_in, dbg_out])
  }

  pub fn with_debug(&mut self, inner: Wire) -> Wire {
    if self.debug {
      let dbg_in = self.net.wire();
      let dbg_out = self.net.wire();
      self.debug_state = Some((dbg_in, dbg_out));
      let ref_ = self.net.make(self.guide.ref_, [dbg_in, dbg_out]);
      self.net.make(self.guide.dbg, [ref_, inner])
    } else {
      inner
    }
  }
}

pub(crate) fn insert_main_net_debug(
  table: &mut Table,
  nets: &mut HashMap<NameId, FlatNet>,
  entrypoint: NameId,
  translator: &Translator<'_>,
) {
  let guide = Guide::build(table);

  let mut net = FlatNet::default();
  let [io_in, io_out, main_io_in, main_io_out, dbg_io_in, dbg_io_out] = net.wires();
  let free = net.make(guide.tuple, [io_in, io_out]);
  net.free.push(free);
  let split = guide.ext.with_payload(1u32).with_children([guide.io_split]);
  net.add(split, io_in, [main_io_in, dbg_io_in]);
  let merge = guide.ext.with_payload(2u32).with_children([guide.io_merge]);
  net.add(merge, main_io_out, [dbg_io_out, io_out]);
  let dbg_state_ref = net.make(guide.ref_, [dbg_io_in, dbg_io_out]);
  let main_io_ref = net.make(guide.ref_, [main_io_in, main_io_out]);
  let main = net.make(guide.graft.with_children([entrypoint]), []);
  let nil = net.make(guide.tuple, []);
  let call = net.make(guide.fn_, [main_io_ref, nil]);
  net.add(guide.dbg, main, [dbg_state_ref, call]);
  translator.translate(table, &mut net);
  nets.insert(guide.main, net);
}
