use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
};

use crate::core::Transaction;
use petgraph::{
    algo::{greedy_feedback_arc_set, is_cyclic_directed, toposort},
    stable_graph::{EdgeIndex, NodeIndex, StableGraph},
    visit::EdgeRef,
};

/// A trait to get Transaction's read and write address set
pub trait TransactionRwSet {
    /// The Address that transaction need to visit
    type Address: Eq + Hash + Clone + Send + Sync + Debug;
    /// Return the read account address set of txns  
    fn read_set(&self) -> HashSet<Self::Address>;
    /// Return the read account address set of txns  
    fn write_set(&self) -> HashSet<Self::Address>;
}

/// Reorder the txns to reduce dependecy, if the dep_graph is cyclic, return a list to show the unsolved dependecy
pub fn transaction_reorder<T>(transactions: &Vec<T>) -> (Vec<T>, Option<Vec<Vec<usize>>>)
where
    T: Transaction + TransactionRwSet + Copy,
{
    let mut dep_graph = construct_dep_graph(transactions);

    // If dep_graph is cyclic, call the cycle elimination to solve cycles
    if is_cyclic_directed(&dep_graph) {
        let removed_edges_set = dep_cycle_elimination(&mut dep_graph);
        let reorder_txns = get_transaction_order(&mut dep_graph, transactions);
        let dep_list = get_dep_list(&dep_graph, &removed_edges_set);

        (reorder_txns, Some(dep_list))
    }
    // Otherwise, reorder transactions directly
    else {
        let reorder_txns = get_transaction_order(&mut dep_graph, transactions);
        (reorder_txns, None)
    }
}

fn construct_dep_graph<T>(transactions: &Vec<T>) -> StableGraph<usize, ()>
where
    T: Transaction + TransactionRwSet + Copy,
{
    // StableGraph does not invalidate any unrelated node or edge indices when items are removed.
    let mut graph = StableGraph::new();

    let mut hash: HashMap<<T as TransactionRwSet>::Address, HashSet<NodeIndex>> = HashMap::new();

    // Build write set
    for transaction in transactions {
        let vertex = graph.add_node(0);
        for w in transaction.write_set() {
            hash.entry(w.clone())
                .or_insert_with(HashSet::new)
                .insert(vertex);
        }
    }

    // Build dependency graph, if r[i] = w[j], add edge from i -> j
    for (i, transaction) in transactions.iter().enumerate() {
        let vi = NodeIndex::new(i);
        for r in transaction.read_set() {
            if let Some(writers) = hash.get(&r) {
                for &vj in writers {
                    if vi != vj {
                        let _ = graph.add_edge(vi, vj, ());
                    }
                }
            }
        }
    }

    graph
}

fn dep_cycle_elimination(graph: &mut StableGraph<usize, ()>) -> Vec<(NodeIndex, NodeIndex)> {
    let g: &StableGraph<usize, ()> = graph.borrow();
    let feedback_arc_set: Vec<EdgeIndex> = greedy_feedback_arc_set(g).map(|e| e.id()).collect();
    let mut removed_edges_set: Vec<(NodeIndex, NodeIndex)> = Vec::new();

    // Remove edges in the feedback arc set
    for edgeid in feedback_arc_set {
        // Add the Remove edges' source and target nodeid in set
        removed_edges_set.push(graph.edge_endpoints(edgeid).unwrap());
        graph.remove_edge(edgeid);
    }

    removed_edges_set
}

fn get_transaction_order<T>(graph: &mut StableGraph<usize, ()>, transactions: &Vec<T>) -> Vec<T>
where
    T: Transaction + TransactionRwSet + Copy,
{
    let g: &StableGraph<usize, ()> = graph.borrow();
    // The cycle eliminated graph can not be cyclic
    assert!(!is_cyclic_directed(g));

    // Reorder the txns with topo_sort
    let transaction_order = toposort(g, None).unwrap();

    let mut reorder_transactions = Vec::with_capacity(transactions.len());
    for (index, nodeid) in transaction_order.into_iter().enumerate() {
        // The node weight shows the new idx of current txns
        let node_weight = graph.node_weight_mut(nodeid).unwrap();
        *node_weight = index;
        // Build the reorder txns list
        reorder_transactions.push(transactions[nodeid.index()]);
    }

    reorder_transactions
}

fn get_dep_list(
    graph: &StableGraph<usize, ()>,
    removed_edges_set: &Vec<(NodeIndex, NodeIndex)>,
) -> Vec<Vec<usize>> {
    let mut dep_list: Vec<Vec<usize>> = vec![Vec::new(); graph.node_count()];

    for (a, b) in removed_edges_set {
        // Get the new order of reserved dependency
        let a_order = graph.node_weight(*a).unwrap();
        let b_order = graph.node_weight(*b).unwrap();
        // The dependency is valid if the order of later node is greater than the previous node.
        if b_order < a_order {
            // Add a to dep[b] to indicate that a needs to be executed after b.
            dep_list[*b_order].push(a_order.clone());
        }
    }

    dep_list
}

#[cfg(test)]
mod test {
    use super::*;
    use petgraph::dot::{Config, Dot};

    #[derive(Clone, Copy, Debug)]
    pub struct SampleTransaction {
        /// transfer money from
        pub from: usize,
        /// transfer money to
        pub to: usize,
        txn_type: usize,
    }

    impl Transaction for SampleTransaction {
        type Key = usize;

        type Value = usize;
    }

    impl TransactionRwSet for SampleTransaction {
        type Address = usize;
        fn read_set(&self) -> HashSet<Self::Address> {
            if self.txn_type == 1 {
                vec![self.from].into_iter().collect()
            } else {
                vec![self.from, self.to].into_iter().collect()
            }
        }
        fn write_set(&self) -> HashSet<Self::Address> {
            if self.txn_type == 1 {
                vec![self.to].into_iter().collect()
            } else {
                vec![self.from, self.to].into_iter().collect()
            }
        }
    }

    impl SampleTransaction {
        fn new(from: usize, to: usize, txn_type: usize) -> SampleTransaction {
            SampleTransaction {
                from: from,
                to: to,
                txn_type: txn_type,
            }
        }
    }

    fn build_test_graph(txn_type: usize) -> (Vec<SampleTransaction>, StableGraph<usize, ()>) {
        let mut v = Vec::new();

        v.push(SampleTransaction::new(1, 2, txn_type));
        v.push(SampleTransaction::new(2, 3, txn_type));
        v.push(SampleTransaction::new(3, 1, txn_type));

        let g = construct_dep_graph(&v);

        (v, g)
    }

    #[test]
    fn test_graph_construct() {
        let mut v = Vec::new();

        for _i in 0..1001 {
            let sample = SampleTransaction::new(100, 101, 0);
            v.push(sample);
        }

        let _graph = construct_dep_graph(&v);

        //println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
    }

    #[test]
    fn test_huge_txns_reorder() {
        let mut v = Vec::new();

        for _i in 0..101 {
            let sample = SampleTransaction::new(100, 101, 0);
            v.push(sample);
        }

        let mut graph = construct_dep_graph(&v);
        println!("build graph finished");

        let result = dep_cycle_elimination(&mut graph);
        println!("{:?}", result.len());

        let _topo_order = get_transaction_order(&mut graph, &mut v);
        println!("build topo_order finished");

        let _dep_list = get_dep_list(&graph, &result);
        println!("build dep_list finished");
    }

    #[test]
    fn test_transaction_reorder() {
        let (transactions, mut graph) = build_test_graph(1);
        let result = dep_cycle_elimination(&mut graph);

        let topo_order = get_transaction_order(&mut graph, &transactions);
        let dep_list = get_dep_list(&graph, &result);

        assert_eq!(result.len(), 1);
        println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
        println!("{:?}", result);
        println!("{:?}", topo_order);
        println!("{:?}", dep_list);

        let (transactions, mut graph) = build_test_graph(0);
        let result = dep_cycle_elimination(&mut graph);
        let topo_order = get_transaction_order(&mut graph, &transactions);
        let dep_list = get_dep_list(&graph, &result);

        assert_eq!(result.len(), 3);
        println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
        println!("{:?}", result);
        println!("{:?}", topo_order);
        println!("{:?}", dep_list);
    }
}
