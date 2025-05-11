use std::{
  collections::{HashMap, HashSet},
  error::Error,
  fmt::{self, Display, Formatter},
};

use anyhow::{bail, Ok, Result};

use crate::ast::{FlowLabel, Net, NetType, Nets, Tree, TreeNode, Type};

#[derive(Debug)]
pub struct FlowAnalysis<'ast> {
  net_types: &'ast HashMap<String, NetType>,
  flow_nodes: Vec<FlowNode<'ast>>,
  var_flow: HashMap<String, Flow>,
}

impl<'ast> Display for FlowAnalysis<'ast> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    for (i, node) in self.flow_nodes.iter().enumerate() {
      writeln!(f, "Node {}: {}", i, node.tree)?;
      writeln!(
        f,
        "    -> {}",
        node.neighbors.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ")
      )?;
    }
    fmt::Result::Ok(())
  }
}

#[derive(Debug)]
pub enum FlowError {
  FlowCycle(Vec<Tree>),
  IncompatibleFlowLabel { incompatible_flow_label: FlowLabel, tree: Tree },
}

impl Display for FlowError {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match &self {
      FlowError::FlowCycle(cycle) => {
        writeln!(f, "Cycle detected in flow graph:")?;
        for tree in cycle {
          writeln!(f, "{tree}")?;
        }
        fmt::Result::Ok(())
      }
      FlowError::IncompatibleFlowLabel { incompatible_flow_label, tree } => {
        writeln!(
          f,
          "Tree {tree} has the incompatible flow with label {incompatible_flow_label} flowing into it"
        )
      }
    }
  }
}

impl Error for FlowError {}

#[derive(Debug, Clone)]
pub struct FlowNode<'ast> {
  tree: &'ast Tree,
  neighbors: Vec<usize>,
  num_incoming_edges: u32,
}

#[derive(Debug, Clone, PartialEq)]
enum Flow {
  /// Flow towards the leafs of the tree
  In(usize),
  /// Flow towards the root of the tree
  Out(usize),
  Pair {
    label: String,
    left: Box<Flow>,
    right: Box<Flow>,
  },
}

impl<'ast> FlowAnalysis<'ast> {
  pub fn analyze_nets(nets: &Nets) -> Result<()> {
    let net_types =
      nets.iter().map(|(name, net)| (name.to_owned(), net.net_type.to_owned())).collect();
    for net in nets.values() {
      FlowAnalysis::analyze_net(net, &net_types)?;
    }
    Ok(())
  }

  pub fn analyze_net(net: &Net, net_types: &HashMap<String, NetType>) -> Result<()> {
    let mut flow_analysis =
      FlowAnalysis { net_types, flow_nodes: Vec::new(), var_flow: HashMap::new() };
    for (tree1, tree2) in &net.pairs {
      let flow1 = flow_analysis.build_flow_graph_tree(tree1);
      let flow2 = flow_analysis.build_flow_graph_tree(tree2);
      flow_analysis.connect_tree_flows(&flow1, &flow2);
    }
    let root_flow = flow_analysis.build_flow_graph_tree(&net.root);

    flow_analysis.detect_cycles()?;
    flow_analysis.check_flow_labels(&root_flow, &net.net_type)
  }

  fn build_flow_graph_tree(&mut self, tree: &'ast Tree) -> Flow {
    let ty = tree.ty.as_ref().unwrap();
    match &tree.tree_node {
      TreeNode::Erase | TreeNode::N32(_) | TreeNode::F32(_) => self.flow_from_type(ty, tree),
      TreeNode::Global(name) => self.flow_from_net_type(&self.net_types[name], tree),
      TreeNode::Var(name) => {
        let flow = self.flow_from_type(ty, tree);
        match self.var_flow.remove(name) {
          // Other end of variable was already visited. Can now connect the two flows.
          Some(other_flow) => {
            self.connect_var_flows(&flow, &other_flow);
          }
          None => {
            self.var_flow.insert(name.to_owned(), flow.clone());
          }
        }
        flow
      }
      TreeNode::ExtFn(_name, _swapped_arguments, arg2, out) => {
        let arg2_flow = self.build_flow_graph_tree(arg2);
        let out_flow = self.build_flow_graph_tree(out);
        let flow = self.flow_from_type(ty, tree);
        self.connect_stacked_flows(&flow, &out_flow);
        self.connect_stacked_flows(&flow, &arg2_flow);
        self.connect_tree_flows(&arg2_flow, &out_flow);
        flow
      }
      TreeNode::Comb(label, left_node, right_node) => match &ty {
        Type::Pair { label: _, .. } => {
          let left_node_flow = self.build_flow_graph_tree(left_node);
          let right_node_flow = self.build_flow_graph_tree(right_node);
          Flow::Pair {
            label: label.to_owned(),
            left: Box::new(left_node_flow),
            right: Box::new(right_node_flow),
          }
        }
        _ => unreachable!("Comb nodes need to have Pair type (checked by type checker)"),
      },
      TreeNode::Branch(zero_branch, positive_branch, out) => {
        let flow = self.flow_from_type(ty, tree);
        let zero_branch_flow = self.build_flow_graph_tree(zero_branch);
        let positive_branch_flow = self.build_flow_graph_tree(positive_branch);
        let out_flow = self.build_flow_graph_tree(out);
        self.connect_stacked_flows(&flow, &zero_branch_flow);
        self.connect_stacked_flows(&flow, &positive_branch_flow);
        self.connect_stacked_flows(&flow, &out_flow);
        self.connect_tree_flows(&zero_branch_flow, &out_flow);
        self.connect_tree_flows(&positive_branch_flow, &out_flow);
        flow
      }
      TreeNode::BlackBox(t) => self.build_flow_graph_tree(t),
    }
  }

  fn new_node(&mut self, tree: &'ast Tree) -> usize {
    let id = self.flow_nodes.len();
    let node = FlowNode { tree, neighbors: Vec::new(), num_incoming_edges: 0 };
    self.flow_nodes.push(node);
    id
  }

  fn flow_from_type(&mut self, ty: &'ast Type, tree: &'ast Tree) -> Flow {
    match ty {
      Type::Out(_) => {
        let node_id = self.new_node(tree);
        Flow::Out(node_id)
      }
      Type::In(_) => {
        let node_id = self.new_node(tree);
        Flow::In(node_id)
      }
      Type::Pair { label, left, right } => {
        let left_flow = self.flow_from_type(left, tree);
        let right_flow = self.flow_from_type(right, tree);
        Flow::Pair {
          label: label.to_owned(),
          left: Box::new(left_flow),
          right: Box::new(right_flow),
        }
      }
    }
  }

  fn flow_from_net_type(&mut self, net_type: &NetType, tree: &'ast Tree) -> Flow {
    let mut flows_in = HashMap::<FlowLabel, HashSet<usize>>::new();
    let mut flows_out = HashMap::<FlowLabel, HashSet<usize>>::new();
    self.flow_from_net_type_aux(net_type, tree, &mut flows_in, &mut flows_out)
  }

  fn flow_from_net_type_aux(
    &mut self,
    net_type: &NetType,
    tree: &'ast Tree,
    flows_in: &mut HashMap<FlowLabel, HashSet<usize>>,
    flows_out: &mut HashMap<FlowLabel, HashSet<usize>>,
  ) -> Flow {
    match net_type {
      NetType::In { ty: _, flow_label } => {
        let node_id = self.new_node(tree);
        flows_in.entry(flow_label.to_owned()).or_default().insert(node_id);
        if let Some(out_nodes) = flows_out.get(flow_label) {
          for out_node in out_nodes {
            self.add_flow_edge(node_id, *out_node);
          }
        }
        Flow::In(node_id)
      }
      NetType::Out { ty: _, flow_labels } => {
        let node_id = self.new_node(tree);
        for flow_label in flow_labels {
          flows_out.entry(flow_label.to_owned()).or_default().insert(node_id);
          if let Some(in_nodes) = flows_in.get(flow_label) {
            for in_node in in_nodes {
              self.add_flow_edge(*in_node, node_id);
            }
          }
        }
        Flow::Out(node_id)
      }
      NetType::Pair { label, left, right } => {
        let left_flow = self.flow_from_net_type_aux(left, tree, flows_in, flows_out);
        let right_flow = self.flow_from_net_type_aux(right, tree, flows_in, flows_out);
        Flow::Pair {
          label: label.to_owned(),
          left: Box::new(left_flow),
          right: Box::new(right_flow),
        }
      }
    }
  }

  // Connect the flows of the two ends of a variable together
  fn connect_var_flows(&mut self, flow1: &Flow, flow2: &Flow) {
    match (flow1, flow2) {
      (Flow::In(node1), Flow::Out(node2)) => {
        self.add_flow_edge(*node1, *node2);
      }
      (Flow::Out(node1), Flow::In(node2)) => {
        self.add_flow_edge(*node2, *node1);
      }
      (
        Flow::Pair { label: label1, left: left1, right: right1 },
        Flow::Pair { label: label2, left: left2, right: right2 },
      ) => {
        if label1 == label2 {
          self.connect_var_flows(left1, left2);
          self.connect_var_flows(right1, right2);
        } else {
          unreachable!("Variable have to have matching flows (checked by type checker)")
        }
      }
      _ => unreachable!("Variable have to have matching flows (checked by type checker)"),
    }
  }

  // Connect to flows that are stacked on top of each other (e.g. the flow of a
  // primary ports and an aux port)
  fn connect_stacked_flows(&mut self, flow_top: &Flow, flow_bottom: &Flow) {
    match (flow_top, flow_bottom) {
      (Flow::In(node_top), Flow::In(node_bottom)) => {
        self.add_flow_edge(*node_top, *node_bottom);
      }
      (Flow::Out(node_top), Flow::Out(node_bottom)) => {
        self.add_flow_edge(*node_bottom, *node_top);
      }
      (Flow::In(_), Flow::Out(_)) | (Flow::Out(_), Flow::In(_)) => {}
      (
        Flow::Pair { label: label_top, left: left_top, right: right_top },
        Flow::Pair { label: label_bottom, left: left_bottom, right: right_bottom },
      ) => {
        if label_top == label_bottom {
          self.connect_stacked_flows(left_top, left_bottom);
          self.connect_stacked_flows(right_top, right_bottom);
        } else {
          panic!("Mismatching flows")
        }
      }
      (single_flow, Flow::Pair { label: _, left, right }) => {
        self.connect_stacked_flows(single_flow, left);
        self.connect_stacked_flows(single_flow, right);
      }
      (Flow::Pair { label: _, left, right }, single_flow) => {
        self.connect_stacked_flows(left, single_flow);
        self.connect_stacked_flows(right, single_flow);
      }
    }
  }

  // Connect the flows of two trees (e.g. primary-to-primary connection or
  // connecting the flows of the aux ports of a binary node)
  fn connect_tree_flows(&mut self, flow1: &Flow, flow2: &Flow) {
    match (flow1, flow2) {
      (Flow::In(node1), Flow::Out(node2)) => {
        self.add_flow_edge(*node2, *node1);
      }
      (Flow::Out(node1), Flow::In(node2)) => {
        self.add_flow_edge(*node1, *node2);
      }
      (Flow::Out(_), Flow::Out(_)) | (Flow::In(_), Flow::In(_)) => {}
      (
        Flow::Pair { label: label1, left: left1, right: right1 },
        Flow::Pair { label: label2, left: left2, right: right2 },
      ) => {
        if label1 == label2 {
          self.connect_tree_flows(left1, left2);
          self.connect_tree_flows(right1, right2);
        } else {
          self.connect_tree_flows(left1, flow2);
          self.connect_tree_flows(left2, flow2);
          self.connect_tree_flows(flow1, right1);
          self.connect_tree_flows(flow1, right2);
        }
      }
      (single_flow, Flow::Pair { label: _, left, right })
      | (Flow::Pair { label: _, left, right }, single_flow) => {
        self.connect_tree_flows(left, single_flow);
        self.connect_tree_flows(right, single_flow);
      }
    }
  }

  fn add_flow_edge(&mut self, from: usize, to: usize) {
    self.flow_nodes[from].neighbors.push(to);
    self.flow_nodes[to].num_incoming_edges += 1;
  }

  fn detect_cycles(&self) -> Result<()> {
    let num_nodes = self.flow_nodes.len();
    let mut visited = vec![false; num_nodes];
    let mut stack = Vec::new();

    for node in 0..num_nodes {
      if !visited[node] {
        self.detect_cycles_dfs(node, &mut visited, &mut stack)?;
      }
    }
    Ok(())
  }

  fn detect_cycles_dfs(
    &self,
    node: usize,
    visited: &mut Vec<bool>,
    stack: &mut Vec<usize>,
  ) -> Result<()> {
    visited[node] = true;
    stack.push(node);

    for &neighbor in &self.flow_nodes[node].neighbors {
      if stack.contains(&neighbor) {
        // This completes a cycle
        let neighbor_first_appearance = stack.iter().position(|&x| x == neighbor).unwrap();
        let cycle = stack[neighbor_first_appearance..].to_vec();
        bail!(FlowError::FlowCycle(
          cycle.iter().map(|&i| self.flow_nodes[i].tree.clone()).collect()
        ));
      }
      if !visited[neighbor] {
        self.detect_cycles_dfs(neighbor, visited, stack)?;
      }
    }
    stack.pop();
    Ok(())
  }

  fn root_flow_labels(
    root_flow: &Flow,
    net_type: &NetType,
  ) -> (HashMap<usize, FlowLabel>, HashMap<usize, Vec<FlowLabel>>) {
    match (root_flow, net_type) {
      (Flow::In(node_idx), NetType::In { flow_label, .. }) => {
        let mut in_flow_labels = HashMap::<usize, FlowLabel>::new();
        in_flow_labels.insert(*node_idx, flow_label.to_owned());
        (in_flow_labels, HashMap::new())
      }
      (Flow::Out(node_idx), NetType::Out { flow_labels, .. }) => {
        let mut out_flow_labels = HashMap::<usize, Vec<FlowLabel>>::new();
        out_flow_labels.insert(*node_idx, flow_labels.to_owned());
        (HashMap::new(), out_flow_labels)
      }
      (
        Flow::Pair { left, right, .. },
        NetType::Pair { label: _, left: left_net_type, right: right_net_type },
      ) => {
        let (mut left_in_flow_labels, mut left_out_flow_labels) =
          FlowAnalysis::root_flow_labels(left, left_net_type);
        let (right_in_flow_labels, right_out_flow_labels) =
          FlowAnalysis::root_flow_labels(right, right_net_type);
        left_in_flow_labels.extend(right_in_flow_labels);
        left_out_flow_labels.extend(right_out_flow_labels);
        (left_in_flow_labels, left_out_flow_labels)
      }
      _ => unreachable!(
        "Root flow did not match the net type. This should have been checked by the type checker"
      ),
    }
  }

  fn check_flow_labels(&self, root_flow: &Flow, net_type: &NetType) -> Result<()> {
    let (root_in_flow_labels, root_out_flow_labels) =
      FlowAnalysis::root_flow_labels(root_flow, net_type);
    let mut todo = Vec::new();
    let mut flows = vec![HashSet::<FlowLabel>::new(); self.flow_nodes.len()];
    for (node_index, flow_label) in root_in_flow_labels {
      todo.push(node_index);
      flows[node_index].insert(flow_label);
    }

    let mut num_unprocessed_predecessors =
      self.flow_nodes.iter().map(|node| node.num_incoming_edges).collect::<Vec<_>>();

    while let Some(node_idx) = todo.pop() {
      let node_flow = flows[node_idx].clone();
      for neighbor_idx in &self.flow_nodes[node_idx].neighbors {
        flows[*neighbor_idx].extend(node_flow.clone());
        num_unprocessed_predecessors[*neighbor_idx] -= 1;
        if num_unprocessed_predecessors[*neighbor_idx] == 0 {
          todo.push(*neighbor_idx);
        }
      }
    }

    for (node_index, flow_labels) in root_out_flow_labels {
      for reaching_flow_label in flows[node_index].iter() {
        if !flow_labels.contains(reaching_flow_label) {
          bail!(FlowError::IncompatibleFlowLabel {
            incompatible_flow_label: reaching_flow_label.to_owned(),
            tree: self.flow_nodes[node_index].tree.clone()
          });
        }
      }
    }

    Ok(())
  }
}
