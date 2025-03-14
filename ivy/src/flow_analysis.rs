use std::{
  collections::{HashMap, HashSet},
  error::Error,
  fmt::{self, Display, Formatter},
};

use anyhow::{bail, Ok, Result};

use crate::ast::{Net, Nets, Polarity, Tree, TreeNode, Type};

#[derive(Default, Debug)]
pub struct FlowAnalysis<'ast> {
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
  IncompatibleLifetimesFlow { incompatible_lifetime: Option<String>, tree: Tree },
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
      FlowError::IncompatibleLifetimesFlow { incompatible_lifetime, tree } => {
        writeln!(
          f,
          "Tree {tree} has the incompatible lifetime {incompatible_lifetime:?} flowing into it"
        )
      }
    }
  }
}

impl Error for FlowError {}

#[derive(Debug, Clone)]
pub struct FlowNode<'ast> {
  tree: &'ast Tree,
  lifetime: &'ast Option<String>,
  neighbors: Vec<usize>,
  num_incoming_edges: u32,
}

#[derive(Debug, Clone, PartialEq)]
enum Flow {
  /// Flow towards the leafs of the tree
  Down(usize),
  /// Flow towards the root of the tree
  Up(usize),
  Pair {
    label: String,
    left: Box<Flow>,
    right: Box<Flow>,
  },
}

impl Flow {
  pub fn flow_nodes(&self) -> Vec<usize> {
    match self {
      Flow::Down(node) | Flow::Up(node) => vec![*node],
      Flow::Pair { left, right, .. } => {
        let mut nodes = left.flow_nodes();
        nodes.extend(right.flow_nodes());
        nodes
      }
    }
  }
}

impl<'ast> FlowAnalysis<'ast> {
  pub fn analyze_nets(nets: &Nets) -> Result<()> {
    for net in nets.values() {
      FlowAnalysis::analyze_net(net)?;
    }
    Ok(())
  }

  pub fn analyze_net(net: &Net) -> Result<()> {
    let mut flow_analysis = FlowAnalysis::default();
    for (tree1, tree2) in &net.pairs {
      let flow1 = flow_analysis.build_flow_graph_tree(tree1);
      let flow2 = flow_analysis.build_flow_graph_tree(tree2);
      flow_analysis.connect_tree_flows(&flow1, &flow2);
    }
    let root_flow = flow_analysis.build_flow_graph_tree(&net.root);

    flow_analysis.detect_cycles()?;
    flow_analysis.detect_incorrect_lifetime_flow(&root_flow)
  }

  fn build_flow_graph_tree(&mut self, tree: &'ast Tree) -> Flow {
    let ty = tree.ty.as_ref().unwrap();
    match &tree.tree_node {
      TreeNode::Erase | TreeNode::N32(_) | TreeNode::F32(_) => self.flow_from_type(ty, tree),
      TreeNode::Global(_) => {
        let flow = self.flow_from_type(ty, tree);
        self.connect_flow_according_to_lifetimes(&flow);
        flow
      }
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

  fn new_node(&mut self, tree: &'ast Tree, lifetime: &'ast Option<String>) -> usize {
    let id = self.flow_nodes.len();
    let node = FlowNode { tree, lifetime, neighbors: Vec::new(), num_incoming_edges: 0 };
    self.flow_nodes.push(node);
    id
  }

  fn flow_from_type(&mut self, ty: &'ast Type, tree: &'ast Tree) -> Flow {
    match ty {
      Type::Primitive { ty: _, polarity: Polarity::Out, lifetime } => {
        let node_id = self.new_node(tree, lifetime);
        Flow::Up(node_id)
      }
      Type::Primitive { ty: _, polarity: Polarity::In, lifetime } => {
        let node_id = self.new_node(tree, lifetime);
        Flow::Down(node_id)
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

  fn connect_flow_according_to_lifetimes(&mut self, flow: &Flow) {
    // Map from each lifetime to the down flow nodes that have that lifetime
    let mut lifetime_down = HashMap::<Option<String>, HashSet<usize>>::new();
    // Map from each lifetime to the up flow nodes that have that lifetime
    let mut lifetime_up = HashMap::<Option<String>, HashSet<usize>>::new();
    self.connect_flow_according_to_lifetimes_aux(flow, &mut lifetime_down, &mut lifetime_up);
  }

  fn connect_flow_according_to_lifetimes_aux(
    &mut self,
    flow: &Flow,
    lifetime_down: &mut HashMap<Option<String>, HashSet<usize>>,
    lifetime_up: &mut HashMap<Option<String>, HashSet<usize>>,
  ) {
    match flow {
      Flow::Down(node) => {
        let lifetime = self.flow_nodes[*node].lifetime.to_owned();
        lifetime_down.entry(lifetime.clone()).or_default().insert(*node);
        if let Some(group_up) = lifetime_up.get(&lifetime) {
          for up_elem in group_up {
            self.add_flow_edge(*node, *up_elem);
          }
        }
      }
      Flow::Up(node) => {
        let lifetime = self.flow_nodes[*node].lifetime.to_owned();
        lifetime_up.entry(lifetime.clone()).or_default().insert(*node);
        if let Some(group_down) = lifetime_down.get(&lifetime) {
          for down_elem in group_down {
            self.add_flow_edge(*down_elem, *node);
          }
        }
      }
      Flow::Pair { left, right, .. } => {
        self.connect_flow_according_to_lifetimes_aux(left, lifetime_down, lifetime_up);
        self.connect_flow_according_to_lifetimes_aux(right, lifetime_down, lifetime_up);
      }
    }
  }

  // Connect the flows of the two ends of a variable together
  fn connect_var_flows(&mut self, flow1: &Flow, flow2: &Flow) {
    match (flow1, flow2) {
      (Flow::Down(node1), Flow::Up(node2)) => {
        self.add_flow_edge(*node1, *node2);
      }
      (Flow::Up(node1), Flow::Down(node2)) => {
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
      (Flow::Down(node_top), Flow::Down(node_bottom)) => {
        self.add_flow_edge(*node_top, *node_bottom);
      }
      (Flow::Up(node_top), Flow::Up(node_bottom)) => {
        self.add_flow_edge(*node_bottom, *node_top);
      }
      (Flow::Down(_), Flow::Up(_)) | (Flow::Up(_), Flow::Down(_)) => {}
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
      (Flow::Down(node1), Flow::Up(node2)) => {
        self.add_flow_edge(*node2, *node1);
      }
      (Flow::Up(node1), Flow::Down(node2)) => {
        self.add_flow_edge(*node1, *node2);
      }
      (Flow::Up(_), Flow::Up(_)) | (Flow::Down(_), Flow::Down(_)) => {}
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

  fn detect_incorrect_lifetime_flow(&self, root_flow: &Flow) -> Result<()> {
    // Start with all root nodes that don't have incoming edges
    let mut todo = root_flow
      .flow_nodes()
      .into_iter()
      .filter(|node_idx| self.flow_nodes[*node_idx].num_incoming_edges == 0)
      .collect::<Vec<_>>();

    let mut lifetimes = HashMap::<usize, HashSet<Option<String>>>::new();
    for node_idx in &todo {
      let lifetime = self.flow_nodes[*node_idx].lifetime.to_owned();
      lifetimes.entry(*node_idx).or_default().insert(lifetime);
    }

    let mut num_unprocessed_predecessors =
      self.flow_nodes.iter().map(|node| node.num_incoming_edges).collect::<Vec<_>>();

    while let Some(node_idx) = todo.pop() {
      let node_lifetimes = lifetimes.get(&node_idx).unwrap().to_owned();
      for neighbor_idx in &self.flow_nodes[node_idx].neighbors {
        lifetimes.entry(*neighbor_idx).or_default().extend(node_lifetimes.clone());
        num_unprocessed_predecessors[*neighbor_idx] -= 1;
        if num_unprocessed_predecessors[*neighbor_idx] == 0 {
          todo.push(*neighbor_idx);
        }
      }
    }

    for node in root_flow.flow_nodes() {
      let node_lifetime = self.flow_nodes[node].lifetime;
      // Check that only the lifetime the node is annotated with can actually reach
      // that node
      if let Some(reaching_lifetimes) = lifetimes.get(&node) {
        for reaching_lifetime in reaching_lifetimes {
          if reaching_lifetime != node_lifetime {
            bail!(FlowError::IncompatibleLifetimesFlow {
              incompatible_lifetime: reaching_lifetime.to_owned(),
              tree: self.flow_nodes[node].tree.clone()
            });
          }
        }
      }
    }

    Ok(())
  }
}
