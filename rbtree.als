open btree
open util/ordering[Event] as ord

abstract sig Color {}
sig Red extends Color {}
sig Black extends Color {}

sig RBNode extends Node {
	color: Color 
}

sig Path {
	t: Tree,
	start: Node,
	end: Node,
	path: seq Node
} {
	// start at start, end at end
	path[0] = start
	path.last = end
	
  // if move down, go in correct direction
  all idx: path.inds - path.lastIdx | {
    let idx' = add[idx, 1] | {
      path[idx].num > end.num implies path[idx'] in t.lefts[path[idx]]
	  path[idx].num < end.num implies path[idx'] in t.rights[path[idx]]
	  path[idx].num = end.num implies no path[idx']
    }
  }  
	
}

fun getReachableLeaves[n : Node, tree: Tree]: set Node {
	// get reachable nodes, intersect with nodes that have no left + nodes that have no right
	n.*(tree.lefts + tree.rights) & ((tree.nodes - tree.lefts.(tree.nodes)) + (tree.nodes - tree.rights.(tree.nodes)))
}

fun getNumBlack[p : Path]: Int {
	#(p.path.elems.color & Black)
}

pred isRedBlackTree[tree: Tree] {
	// has all the properties of a BST
	isBSTree[tree]

	// for convenience, we want all nodes to have their own color sig
	no disj n1, n2 : tree.nodes | n1.color = n2.color

	// all nodes are either red or black
	all n : tree.nodes | n in RBNode

	// root is black
	no tree.root or tree.root.color in Black

	// if a node is red, its children are black
	all n : tree.nodes | n.color in Red implies n.(tree.lefts + tree.rights).color in Black
	
	// for every node, there is a path from itself to every leaf that it can reach
	all startNode : tree.nodes | all endNode : getReachableLeaves[startNode, tree] | {
		one p: Path | p.start = startNode and p.end = endNode and p.t = tree
	}

	all disj p1, p2 : Path | p1.start = p2.start implies getNumBlack[p1] = getNumBlack[p2]
}

run isRedBlackTree for 1 Tree, exactly 7 Node, 7 Color, 0 Descent, 0 AddNode, 12 Path, 0 Event

// check transitions
fact transitions {
	all e : Event-ord/last |
		let e' = e.ord/next | {
			e.post.nodes.num = e'.pre.nodes.num
		}
}

pred testaddrb {
	some a: AddNode | {
		isRedBlackTree[a.pre]
		isRedBlackTree[a.post]
    	a.pre != a.post
    	some a.pre.nodes
	}
}
run testaddrb for exactly 2 Tree, exactly 7 Node, 7 Color, 1 Descent, 1 AddNode, 0 RemoveNode, 12 Path, exactly 1 Event

pred testremoverb {
	some a: RemoveNode | {
		isRedBlackTree[a.pre]
		isRedBlackTree[a.post]
    	a.pre != a.post
    	some a.pre.nodes
	}
}
run testremoverb for exactly 2 Tree, exactly 7 Node, 7 Color, 1 Descent, 0 AddNode, 1 RemoveNode, 12 Path, exactly 1 Event

pred testsequence {
	all e : Event | {
		isRedBlackTree[e.pre]
		isRedBlackTree[e.post]
    	e.pre != e.post
		some e.pre.nodes

		e in AddNode implies e.toadd not in e.pre.nodes.num
		e in RemoveNode implies e.toremove in e.pre.nodes.num
	}
}

run testsequence for exactly 3 Tree, 15 Node, 15 Color, 4 Descent, 12 Path, exactly 2 Event

assert allPathLengthsGood {
	all tree : Tree { 
		isRedBlackTree[tree] implies no disj d1, d2 : Descent | {
			// both on the same tree
			d1.t = tree
			d2.t = tree
			// looking for different values
			d1.val != d2.val
			// neither one finds their value: we want them to search to a leaf
			d1.path.last.num != d1.val
			d2.path.last.num != d2.val
			// they both contain different number of black nodes
			#(d1.path.elems.color & Black) != #(d2.path.elems.color & Black)
		}
	}
}

check allPathLengthsGood for 1 Tree, exactly 5 Node, 5 Color, 6 Descent, 0 AddNode, 6 Path, 0 Event
