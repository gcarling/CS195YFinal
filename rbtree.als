open btree

abstract sig Color {}
sig Red extends Color {}
sig Black extends Color {}

sig RBNode extends Node {
	color: Color 
}

sig Path {
	tree: Tree,
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
      path[idx].num > end.num implies path[idx'] in tree.lefts[path[idx]]
	  path[idx].num < end.num implies path[idx'] in tree.rights[path[idx]]
	  path[idx].num = end.num implies no path[idx']
    }
  }
}

fun getReachableLeaves[n : Node, t: Tree]: set Node {
	// get reachable nodes, intersect with nodes that have no left + nodes that have no right
	n.*(t.lefts + t.rights) & ((t.nodes - t.lefts.(t.nodes)) + (t.nodes - t.rights.(t.nodes)))
}

fun getNumBlack[p : Path]: Int {
	#(p.path.elems.color & Black)
}

pred isRBTree[t: Tree] {
	// has all the properties of a BST
	isBSTree[t]

	// for convenience, we want all nodes to have their own color sig
	no disj n1, n2 : t.nodes | n1.color = n2.color

	// all nodes are either red or black
	all n : t.nodes | n in RBNode

	// root is black
	no t.root or t.root.color in Black

	// if a node is red, its children are black
	all n : t.nodes | n.color in Red implies n.(t.lefts + t.rights).color in Black
	
	// for every node, there is a path from itself to every leaf that it can reach
	all startNode : t.nodes | all endNode : getReachableLeaves[startNode, t] | {
		one p: Path | p.start = startNode and p.end = endNode and p.tree = t
	}

	// all paths from the root to any leaf have the same number of black nodes
	all disj p1, p2 : Path | p1.start = t.root and p2.start = t.root implies getNumBlack[p1] = getNumBlack[p2]
}

run isRBTree for 1 Tree, exactly 7 Node, 7 Color, 0 Descent, 0 AddNode, 12 Path, 0 Event

///////////// Depth Checks ///////////////////

assert allPathLengthsGood {
	all t : Tree | { 
		isRBTree[t] implies no disj d1, d2 : Descent | {
			// both on the same tree
			d1.tree = t
			d2.tree = t
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
check allPathLengthsGood for exactly 1 Tree, 7 Node, 7 Color, 2 Descent, 7 Path, 0 Event

assert noDoubleLengthDescents {
	all t : Tree | { 
		isRBTree[t] implies no disj d1, d2 : Descent | {
			// both on the same tree
			d1.tree = t
			d2.tree = t
			// looking for different values
			d1.val != d2.val
			// neither one finds their value: we want them to search to a leaf
			d1.path.last.num != d1.val
			d2.path.last.num != d2.val
			// neither is twice the length of the other
			#(d1.path.elems) > mul[2, #(d2.path.elems)]
			#(d2.path.elems) > mul[2, #(d1.path.elems)]
		}
	}
}
check noDoubleLengthDescents for exactly 1 Tree, 5 Node, 5 Color, 10 Descent, 10 Path, 0 Event

// it should hold that not just from the root down but any node down there are same # of black nodes
assert allPathsSameNumBlacks {
		all t : Tree | {
			isRBTree[t] implies all disj p1, p2 : Path | p1.start = p2.start implies getNumBlack[p1] = getNumBlack[p2]
		}
}
check allPathsSameNumBlacks for exactly 1 Tree, 5 Node, 5 Color, 0 Descent, 10 Path, 0 Event

///////////// Events ///////////////////

// We didn't end up using this after we bailed on trying to do add/remove for the augmented trees due to the complexity involved with Alloy

pred testaddrb {
	some a: AddNode | {
		isRBTree[a.pre]
		isRBTree[a.post]
    	a.pre != a.post
    	some a.pre.nodes
	}
}
run testaddrb for exactly 2 Tree, exactly 7 Node, 7 Color, 1 Descent, 1 AddNode, 0 RemoveNode, 12 Path

pred testremoverb {
	some a: RemoveNode | {
		isRBTree[a.pre]
		isRBTree[a.post]
    	a.pre != a.post
    	some a.pre.nodes
	}
}
run testremoverb for exactly 2 Tree, exactly 7 Node, 7 Color, 1 Descent, 0 AddNode, 1 RemoveNode, 12 Path
