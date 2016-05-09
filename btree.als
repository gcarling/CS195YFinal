// For use with RB trees

sig Tree {  
	nodes: set Node,
	root: lone nodes,
    lefts, rights: nodes -> lone nodes
} {
	some nodes implies some root
	all n : nodes | n.tree = this
}

run {some Tree} for 3 but 1 Tree

fact allNodesInSomeTree {
	all n: Node |
		one t: Tree | 
			n in t.nodes		
}


/*sig Node {
  num: Int
}*/


sig Node {
  tree: one Tree,	
  num: Int,
  left: lone Node,
  right: lone Node
} {
	left = tree.lefts[this] and
	right = tree.rights[this]
	tree = nodes.this
}


fact NodesUnique {
	all disj n1, n2: Node | n1.tree = n2.tree implies n1.num != n2.num
}

run {} for exactly 1 Tree, 6 Node, 0 Descent, 0 Event

pred isBTree[t: Tree] {
	// root reaches everything
	t.nodes in t.root.*(t.lefts + t.rights)

  all n: t.nodes | {
	  // no cycles
		n not in n.^(t.lefts+t.rights) 
    // at most one parent for each node
		lone n.~(t.lefts+t.rights)
    
    // distinct children if any
		//n.left != n.right // fails if using no left/right instead of Empty 
    no t.lefts[n] & t.rights[n]
  }
}

run isBTree for exactly 8 Node, 1 Tree, 0 Descent, 0 Event

// search tree, so no worries about equal
pred isOrderedTree[t: Tree] {
	all n: Node, n': t.lefts[n].*(t.lefts+t.rights) | 
		n.num > n'.num
	all n: Node, n': t.rights[n].*(t.lefts+t.rights) |
		n.num < n'.num
}

pred isBSTree[t: Tree] {
	isBTree[t]
	isOrderedTree[t]
}
pred testIsBSTree {
	some disj t1,t2: Tree | 
		isBSTree[t1] and isBSTree[t2]
}

run testIsBSTree for 2 Tree, exactly 8 Node, 1 Descent, 0 Event

sig Descent {
	tree: Tree,
	val: Int,
	path: seq Node
} {
	// start at root
	path[0] = tree.root

	// stop only when found or no ref to follow
	let l = path[path.lastIdx] | {
		l.num > val => no l.(tree.lefts)
		l.num < val => no l.(tree.rights)
	}
	
  // if move down, go in correct direction
  all idx: path.inds - path.lastIdx | {
    let idx' = add[idx, 1] | {
      path[idx].num > val implies path[idx'] in tree.lefts[path[idx]]
	    path[idx].num < val implies path[idx'] in tree.rights[path[idx]]
			path[idx].num = val implies no path[idx']
    }
  }  

}

pred testDescentForFound {
	some d: Descent | {
		isBSTree[d.tree]
		d.path[d.path.lastIdx].num = d.val
		interestingTree[d.tree]
		#d.path.elems > 3
	}
}

pred testDescentForNotFound {
	some d: Descent | {
		isBSTree[d.tree]
		d.path[d.path.lastIdx].num != d.val
		interestingTree[d.tree]
  	#d.path.elems > 3
	}
}

run testDescentForFound for 1 Tree, 10 Node, exactly 1 Descent, 5 seq, 0 Event
run testDescentForNotFound for 1 Tree, 10 Node, exactly 1 Descent, 5 seq, 0 Event


pred interestingTree[t: Tree] {
	some n : t.nodes | {
		some t.lefts[n]
		some t.rights[n]
	}
}

assert findIfThere {
	all d: Descent |
		isBSTree[d.tree] implies
		(d.val in d.tree.nodes.num	=>
			d.path[d.path.lastIdx].num = d.val else
			d.path[d.path.lastIdx].num != d.val)
}
check findIfThere for 1 Tree, 6 Node, exactly 1 Descent, 4 seq, 0 Event

//////////////////////////////////////////////////

abstract sig Event {
	pre, post: one Tree
}
sig AddNode extends Event {
	toadd: one Int,
	finding: one Descent
}{
  	no pre.root => 
		{
    	one post.nodes
    	post.nodes.num = toadd
		}
	else  {
		finding.val = toadd
    	finding.tree = pre
    
    	finding.path.last.num = finding.val => 
			pre.nodes.num = post.nodes.num
		else pre.nodes.num + toadd = post.nodes.num
	}
}

pred testadd {
	one a: AddNode | {
		isBSTree[a.pre]
		isBSTree[a.post]
    	a.pre != a.post
    	some a.pre.nodes
	}
}

run testadd for exactly 9 Node, 4 seq, 1 AddNode, 0 RemoveNode, 1 Descent, 2 Tree

assert addlength {
	all a: AddNode | {
		a.finding.path.last.num != a.toadd implies
    	#(a.pre.nodes) = sub[#(a.post.nodes), 1]
  }
}
// **** Oops: Make sure to give long-enough sequences to actually reach the
// leaf node we need to add to. Failing to do that will make the property fail.
check addlength for 2 Tree, 1 AddNode, 0 RemoveNode, 1 Descent, 5 seq, 4 int, 5 Node

/////////////////

sig RemoveNode extends Event {
	toremove: one Int,
	finding: one Descent
}{
  	no pre.root => 
		{
    	pre = post
    	finding.tree = pre
		}
	else {
		finding.val = toremove
    	finding.tree = pre
    
    	finding.path.last.num != finding.val => 
			pre.nodes.num = post.nodes.num
		else post.nodes.num = pre.nodes.num - toremove
	}
}

pred testremove {
	some r: RemoveNode | {
		isBSTree[r.pre]
		isBSTree[r.post]
    	r.pre.nodes != r.post.nodes
    	some r.pre.nodes
	}
}
run testremove for exactly 9 Node, 4 seq, 0 AddNode, 1 RemoveNode, 1 Descent, 2 Tree

assert removelength {
	all r: RemoveNode | {
		r.finding.path.last.num = r.toremove implies
    	#(r.pre.nodes) = add[#(r.post.nodes), 1]
  }
}
// **** Oops: Make sure to give long-enough sequences to actually reach the
// leaf node we need to add to. Failing to do that will make the property fail.
check removelength for 2 Tree, 1 RemoveNode, 0 AddNode, 1 Descent, 5 seq, 4 int, 5 Node

