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

pred isAVLTree[t: Tree] {
	// has all the properties of a BST
	isBSTree[t]

	// made of AVLNode
	t.nodes in AVLNode
	
	// balance_factor checked
	all n: t.nodes |
		within1[n.balance_factor, 0]
}

run isAVLTree for 1 Tree, exactly 5 Node, 0 Descent, 0 AddNode, 0 Event, 3 Int

fun max[i1: Int, i2: Int] : Int {
	i1 > i2 => i1
	else i2
}
pred within1[i1: Int, i2: Int] {
	i1 = i2 or
	i1 = add[i2, 1] or
	i1 = sub[i2,1]
}
/*
fun getDepth[t: Tree, n: Node] : Int {
	let L = t.lefts[n] |
	let R = t.rights[n] | {
		(no L and no R) => 0
		else {
			no L => add[getDepth[t, R], 1]
			else {
				no R => add[getDepth[t, L], 1]
				else { 
					let leftmax = getDepth[t, L] |
					let rightmax = getDepth[t, R] |
						leftmax > rightmax => add[leftmax, 1]
						else add[rightmax, 1]
				}
			}
		}
	}
}

assert proper_depths {
	all t: Tree | {
		isAVLTree[t] =>
		(all n: AVLNode |
			let L = n.left |
			let R = n.right | 
			let leftmax = getDepth[t, L] |
			let rightmax = getDepth[t, R] | {
				(no L and no R) or
				(no L and rightmax <= 1) or
				(no R and leftmax <= 1) or
				within1[getDepth[t, L], getDepth[t, R]]
			}
		)
	}
}
check proper_depths for exactly 1 Tree, 5 Node, 0 Descent, 0 Event
*/

pred testaddAVL {
	some a: AddNode | {
		isAVLTree[a.pre]
		isAVLTree[a.post]
    	#(a.pre.nodes) != #(a.post.nodes)
    	some a.pre.nodes
	}
}
run testaddAVL for exactly 2 Tree, 9 Node, 1 Descent, 1 AddNode, exactly 1 Event

pred addAVL {
	some a: AddNode | {
		isAVLTree[a.pre]
		}
}
run addAVL for exactly 3 Tree, 14 Node, 1 Descent, 1 AddNode, exactly 1 Event

assert AVLinvariant {
	addAVL implies isAVLTree[a.post]
}
check AVLinvariant for 2 Tree, 7 Node, 1 Descent, 1 AddNode, 0 RemoveNode


