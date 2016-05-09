open btree

sig AVLNode extends Node {
	depth: Int,
	balance_factor: Int
}
fact definitions {
	all n : AVLNode | {
		(no n.left and no n.right) implies
			(n.depth = 1 and
			n.balance_factor = 0)
		(no n.left and some n.right) implies
			(n.depth = add[n.right.depth, 1] and
			n.balance_factor = sub[0, n.right.depth])
		(no n.right and some n.left) implies
			(n.depth = add[n.left.depth, 1] and
			n.balance_factor = n.left.depth)
		(some right and some left) implies
			(n.depth = add[max[n.left.depth, n.right.depth], 1] and
			n.balance_factor = sub[n.left.depth, n.right.depth])
	}
}

fun max[i1: Int, i2: Int] : Int {
	i1 > i2 => i1
	else i2
}
pred within1[i1: Int, i2: Int] {
	i1 = i2 or
	i1 = add[i2, 1] or
	i1 = sub[i2,1]
}

pred isAVLTree[t: Tree] {
	// has all the properties of a BST
	isBSTree[t]

	// made of AVLNode
	t.nodes in AVLNode
	
	// balance_factor checked
	all n: t.nodes |
		within1[n.balance_factor, 0]
}
run isAVLTree for 1 Tree, exactly 5 Node, 0 Descent, 0 Event, 3 Int

///////////// Depth Checks ///////////////////

assert noDoubleLengthDescents {
	all t : Tree { 
		isAVLTree[t] implies no disj d1, d2 : Descent | {
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
check noDoubleLengthDescents for 4 Int, exactly 1 Tree, 7 Node, 2 Descent, 0 Event

assert logdepthAVL {
	all t: Tree | {
		isAVLTree[t] implies {
			#t.nodes = 2 implies t.root.depth = 2
			#t.nodes = 3 implies t.root.depth = 2
			#t.nodes = 4 implies t.root.depth = 3
			#t.nodes = 5 implies t.root.depth = 3
			#t.nodes = 6 implies t.root.depth = 3
			#t.nodes = 7 implies t.root.depth <= 4
			#t.nodes = 8 implies t.root.depth <= 4
			#t.nodes = 9 implies t.root.depth <= 4
			#t.nodes = 10 implies t.root.depth <= 4
			#t.nodes = 11 implies t.root.depth <= 4
			#t.nodes = 12 implies t.root.depth <= 5
		}
	}
}
check logdepthAVL for 1 Tree, 12 Node, 0 Descent, 0 Event, 5 Int

pred depth5AVL[t: Tree] {
	isAVLTree[t]
	t.root.depth = 5
}
run depth5AVL for 1 Tree, 12 Node, 0 Descent, 0 Event, 5 Int

///////////// Events ///////////////////

pred testaddAVL {
	one a: AddNode | {
		isAVLTree[a.pre]
		isAVLTree[a.post]
		#a.pre.nodes != #a.post.nodes
	}
}
run testaddAVL for exactly 2 Tree, 9 Node, 1 Descent, 1 AddNode, exactly 1 Event

/*
pred addAVL {
	some a: AddNode | {
		isAVLTree[a.pre]
		}
}
run addAVL for exactly 3 Tree, 14 Node, 1 Descent, 1 AddNode, exactly 1 Event

assert AVLinvariant {
	all a: AddNode |
		isAVLTree[a.pre] implies isAVLTree[a.post]
}
check AVLinvariant for 2 Tree, 7 Node, 1 Descent, 1 AddNode, 0 RemoveNode
*/

