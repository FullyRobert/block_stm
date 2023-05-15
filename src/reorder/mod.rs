use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
};

use crate::core::{Transaction, TransactionRwSet};
use petgraph::{
    algo::{greedy_feedback_arc_set, is_cyclic_directed, toposort},
    graphmap::DiGraphMap,
    stable_graph::NodeIndex,
    visit::EdgeRef,
};

/// Reorder the txns to reduce dependecy, if the dep_graph is cyclic, return a list to show the unsolved dependecy
pub fn transaction_reorder<T>(transactions: &Vec<T>) -> (Vec<T>, Option<Vec<Vec<usize>>>)
where
    T: Transaction + TransactionRwSet + Copy,
{
    let mut dep_graph = construct_dep_graph(transactions);

    // If dep_graph is cyclic, call the cycle elimination to solve cycles
    if is_cyclic_directed(&dep_graph) {
        let removed_edges_set = dep_cycle_elimination(&mut dep_graph);
        let (reorder_txns, hash) = get_transaction_order(&mut dep_graph, transactions);
        let dep_list = get_dep_list(&dep_graph, &removed_edges_set, &hash);

        (reorder_txns, Some(dep_list))
    }
    // Otherwise, reorder transactions directly
    else {
        let (reorder_txns, _hash) = get_transaction_order(&mut dep_graph, transactions);
        (reorder_txns, None)
    }
}

fn construct_dep_graph<T>(transactions: &Vec<T>) -> DiGraphMap<NodeIndex, ()>
where
    T: Transaction + TransactionRwSet + Copy,
{
    // DiGraphMap does not allow duplicate edges, NodeIndex is needed in the cycle eliminate
    let mut graph =
        DiGraphMap::with_capacity(transactions.len(), transactions.len() * transactions.len());

    let mut hash: HashMap<<T as TransactionRwSet>::Address, HashSet<NodeIndex>> = HashMap::new();

    // Build write set
    for (i, transaction) in transactions.iter().enumerate() {
        let vertex = graph.add_node(NodeIndex::new(i));
        for w in transaction.write_set() {
            hash.entry(w.clone())
                .or_insert_with(|| HashSet::with_capacity(transactions.len()))
                .insert(vertex);
        }
    }

    // Build dependency graph, if r[i] = w[j], add edge from i -> j
    for (i, transaction) in transactions.iter().enumerate() {
        let vi = NodeIndex::new(i);
        for r in transaction.read_set() {
            if let Some(writers) = hash.get(&r) {
                for &vj in writers {
                    // Avoid self-cycles
                    if vi != vj {
                        let _ = graph.add_edge(vi, vj, ());
                    }
                }
            }
        }
    }
    graph
}

fn dep_cycle_elimination(graph: &mut DiGraphMap<NodeIndex, ()>) -> Vec<(NodeIndex, NodeIndex)> {
    let feedback_arc_set: Vec<(NodeIndex, NodeIndex)> =
        greedy_feedback_arc_set(&*graph).map(|e| e.id()).collect();

    // Remove edges of the feedback arc set in graph
    for edgeid in &feedback_arc_set {
        graph.remove_edge(edgeid.0, edgeid.1);
    }

    feedback_arc_set
}

fn get_transaction_order<T>(
    graph: &mut DiGraphMap<NodeIndex, ()>,
    transactions: &Vec<T>,
) -> (Vec<T>, HashMap<NodeIndex, usize>)
where
    T: Transaction + TransactionRwSet + Copy,
{
    let g: &DiGraphMap<NodeIndex, ()> = graph.borrow();
    // The cycle eliminated graph can not be cyclic
    assert!(!is_cyclic_directed(g));

    // Reorder the txns with topo_sort
    let transaction_order = toposort(g, None).unwrap();
    let mut hash = HashMap::with_capacity(transactions.len());

    let mut reorder_transactions = Vec::with_capacity(transactions.len());
    for (index, nodeid) in transaction_order.into_iter().enumerate() {
        // Record the new location of txns
        hash.insert(nodeid, index);
        reorder_transactions.push(transactions[nodeid.index()]);
    }

    (reorder_transactions, hash)
}

fn get_dep_list(
    graph: &DiGraphMap<NodeIndex, ()>,
    removed_edges_set: &Vec<(NodeIndex, NodeIndex)>,
    hash: &HashMap<NodeIndex, usize>,
) -> Vec<Vec<usize>> {
    let mut dep_list: Vec<Vec<usize>> = vec![Vec::new(); graph.node_count()];

    for (a, b) in removed_edges_set {
        // Get the new order of reserved dependency
        let a_order = hash.get(a);
        let b_order = hash.get(b);
        // The dependency is valid if the order of later node is greater than the previous node.
        if b_order < a_order {
            // Add a to dep[b] to indicate that a needs to be executed after b.
            if let (Some(a_order), Some(b_order)) = (a_order, b_order) {
                dep_list[*b_order].push(*a_order);
            }
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

    fn build_test_graph(txn_type: usize) -> (Vec<SampleTransaction>, DiGraphMap<NodeIndex, ()>) {
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

        for _i in 0..1000 {
            let sample = SampleTransaction::new(100, 101, 0);
            v.push(sample);
        }

        let _graph = construct_dep_graph(&v);

        //println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
    }

    #[test]
    fn test_huge_txns_reorder() {
        let mut v = Vec::new();

        for _i in 0..1000 {
            let sample = SampleTransaction::new(100, 101, 0);
            v.push(sample);
        }

        let mut graph = construct_dep_graph(&v);
        // The directed complete graph have n * (n - 1) nodes
        assert_eq!(graph.edge_count(), v.len() * (v.len() - 1));
        println!("build graph finished");

        let result = dep_cycle_elimination(&mut graph);
        // The directed complete graph have n * (n - 1)/2 cycles
        assert_eq!(graph.edge_count(), v.len() * (v.len() - 1) / 2);
        println!("{:?}", result.len());

        let (_topo_order, hash) = get_transaction_order(&mut graph, &mut v);
        println!("build topo_order finished");

        let _dep_list = get_dep_list(&graph, &result, &hash);
        println!("build dep_list finished");
    }

    #[test]
    fn test_transaction_reorder() {
        let (transactions, mut graph) = build_test_graph(1);
        let result = dep_cycle_elimination(&mut graph);

        let (topo_order, hash) = get_transaction_order(&mut graph, &transactions);
        let dep_list = get_dep_list(&graph, &result, &hash);

        assert_eq!(result.len(), 1);
        println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
        println!("{:?}", result);
        println!("{:?}", topo_order);
        println!("{:?}", dep_list);

        let (transactions, mut graph) = build_test_graph(0);
        let result = dep_cycle_elimination(&mut graph);
        let (topo_order, hash) = get_transaction_order(&mut graph, &transactions);
        let dep_list = get_dep_list(&graph, &result, &hash);

        assert_eq!(result.len(), 3);
        println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
        println!("{:?}", result);
        println!("{:?}", topo_order);
        println!("{:?}", dep_list);
    }
}
