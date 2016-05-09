open btree

abstract sig Color {}
sig Red extends Color {}
sig Black extends Color {}

sig RBNode extends Node {
	color: Color,
	nblacks: Int,
	depth: Int
}
fact countblacks {
	all n: RBNode |
		(no n.left or no n.right) => {
			n.color in Black =>
				n.nblacks = 1
			else
				n.nblacks = 0
			}
		else {
			n.color in Black =>
				n.nblacks = add[n.left.nblacks, 1]
			else
				n.nblacks = n.left.nblacks
		}
}
fact definedepth {
	all n : RBNode | {
		(no n.left and no n.right) implies n.depth = 1
		(no n.left and some n.right) implies n.depth = add[n.right.depth, 1]
		(no n.right and some n.left) implies n.depth = add[n.left.depth, 1]
		(some right and some left) implies n.depth = add[max[n.left.depth, n.right.depth], 1]
		}
}

fun max[i1: Int, i2: Int] : Int {
	i1 > i2 => i1
	else i2
}

pred isRBTree[tree: Tree] {
	// has all the properties of a BST
	isBSTree[tree]

	// for convenience, we want all nodes to have their own color sig
	no disj n1, n2 : tree.nodes | n1.color = n2.color

	// all nodes are either red or black
	tree.nodes in RBNode

	// root is black
	no tree.root or tree.root.color in Black

	// if a node is red, its children are black
	all n : tree.nodes | n.color in Red implies n.(tree.lefts + tree.rights).color in Black
	
	// for every node, there is a path from itself to every leaf that it can reach
	all n: tree.nodes | {
		(no n.left and some n.right) implies n.right.nblacks = 0
		(some n.left and no n.right) implies n.left.nblacks = 0
		(some n.left and some n.right) implies n.left.nblacks = n.right.nblacks
	}
}

run isRBTree for 1 Tree, exactly 7 Node, 7 Color, 0 Descent, 0 Event

////////////// Depth Checks //////////////////

assert noDoubleLengthPaths {
	all t: Tree |
		isRBTree[t] implies {
			no n: t.nodes |
				n.left.depth > add[mul[2, n.right.depth], 1] or
				n.right.depth > add[mul[2, n.left.depth], 1]
		}
}
check noDoubleLengthPaths for 1 Tree, 7 Node, 7 Color, 0 Descent, 0 Event, 4 Int

assert noDoubleLengthDescents {
	all t : Tree { 
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
			#(d1.path.elems) <= mul[2, #(d2.path.elems)]
			#(d2.path.elems) <= mul[2, #(d1.path.elems)]
		}
	}
}
check noDoubleLengthDescents for 4 Int, exactly 1 Tree, 7 Node, 7 Color, 2 Descent, 0 Event

assert logdepthRB {
	all t: Tree | {
		isRBTree[t] implies {
			#t.nodes = 2 implies t.root.depth = 2
			#t.nodes = 3 implies t.root.depth = 2
			#t.nodes = 4 implies t.root.depth = 3
			#t.nodes = 5 implies t.root.depth = 3
			#t.nodes = 6 implies t.root.depth <= 4
			#t.nodes = 7 implies t.root.depth <= 4
			#t.nodes = 8 implies t.root.depth <= 4
			#t.nodes = 9 implies t.root.depth <= 4
			#t.nodes = 10 implies t.root.depth <= 5
			#t.nodes = 11 implies t.root.depth <= 5
			#t.nodes = 12 implies t.root.depth <= 5
		}
	}
}
check logdepthRB for 1 Tree, 10 Node, 10 Color, 0 Descent, 0 Event, 5 Int

pred depth5RB[t: Tree] {
	isRBTree[t]
	t.root.depth = 5
}
run depth5RB for 1 Tree, 12 Node, 12 Color, 0 Descent, 0 Event, 5 Int
