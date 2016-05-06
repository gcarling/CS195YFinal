// March 4th

sig Tree {  
	nodes: set Node,
	root: lone nodes,
    lefts, rights: nodes -> lone nodes
} {
	some nodes implies some root
}

run {some Tree} for 3 but 1 Tree

fact allNodesInSomeTree {
	all n: Node |
		some t: Tree | 
			n in t.nodes		
}


/*sig Node {
  num: Int
}*/



sig Node {
  num: Int,
  left: lone Node,
  right: lone Node
}
fact correctChildren {
	all n: Node |
		n.left = Tree.lefts[n] and
		n.right = Tree.rights[n]
}


fact NodesUnique {
	all disj n1, n2: Node | n1.num != n2.num
}

run {} for 1 Tree, 6 Node, 0 Descent, 0 Event

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
	t: Tree,
	val: Int,
	path: seq Node
} {
	// start at root
	path[0] = t.root

	// stop only when found or no ref to follow
	let l = path[path.lastIdx] | {
		l.num > val => no l.(t.lefts)
		l.num < val => no l.(t.rights)
	}
	
  // if move down, go in correct direction
  all idx: path.inds - path.lastIdx | {
    let idx' = add[idx, 1] | {
      path[idx].num > val implies path[idx'] in t.lefts[path[idx]]
	    path[idx].num < val implies path[idx'] in t.rights[path[idx]]
			path[idx].num = val implies no path[idx']
    }
  }  

}

pred testDescentForFound {
	some d: Descent | {
		isBSTree[d.t]
		d.path[d.path.lastIdx].num = d.val
		interestingTree[d.t]
		#d.path.elems > 3
	}
}

pred testDescentForNotFound {
	some d: Descent | {
		isBSTree[d.t]
		d.path[d.path.lastIdx].num != d.val
		interestingTree[d.t]
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
		isBSTree[d.t] implies
		(d.val in d.t.nodes.num	=>
			d.path[d.path.lastIdx].num = d.val else
			d.path[d.path.lastIdx].num != d.val)
}
check findIfThere for 1 Tree, 6 Node, exactly 1 Descent, 4 seq

//////////////////////////////////////////////////

abstract sig Event {}
sig AddNode extends Event {
	pre, post: one Tree,
	toadd: one Int,
	finding: one Descent
}{
  	no pre.root => 
		{
    	one post.nodes
    	no post.lefts
    	no post.rights
    	post.nodes.num = toadd
		}
	else  {
		finding.val = toadd
    	finding.t = pre
		pre.root = post.root
    
    	finding.path.last.num = finding.val => 
    		{
      		pre = post // or... pre.lefts = post.lefts ...
    		}
		else {
    		let lastdata = finding.path.last | 
				some newnode: Node - pre.nodes | { // n = new Node()
					newnode.num = toadd

        			// no unwanted new nodes
        			post.nodes = pre.nodes + newnode      

        			lastdata.num < toadd implies {
        			  	post.rights = pre.rights + (lastdata -> newnode)
						post.lefts = pre.lefts
       				}

					lastdata.num > toadd implies {
        			    post.lefts = pre.lefts + (lastdata -> newnode)
						post.rights = pre.rights
					}
				}
		}
	}
}

pred testadd {
	some a: AddNode | {
		isBSTree[a.pre]
    	a.pre != a.post
    	some a.pre.nodes
	}
}
run testadd for exactly 6 Node, 4 seq, 1 AddNode, 0 RemoveNode, 1 Descent, 2 Tree

assert addpreserves {
	all a: AddNode | {
    isBSTree[a.pre] implies isBSTree[a.post]
  }
}
// **** Oops: Make sure to give long-enough sequences to actually reach the
// leaf node we need to add to. Failing to do that will make the property fail.
check addpreserves for 2 Tree, 1 AddNode, 0 RemoveNode, 1 Descent, 5 seq, 4 int, 5 Node

/////////////////

sig RemoveNode extends Event {
	pre, post: one Tree,
	toremove: one Int,
	finding: one Descent
}{
  	no pre.root => 
		{
    	no post.nodes
		}
	else {
		finding.val = toremove
    	finding.t = pre
		pre.root = post.root
    
    	finding.path.last.num != finding.val => 
    		{
      		pre = post
    		}
		else {
			let penult = finding.path.butlast.last |
				some oldnode: Node - post.nodes | {
					oldnode.num = toremove

        			// no unwanted removed nodes
        			post.nodes = pre.nodes - oldnode      

        			oldnode.num < penult.num implies {
        			  	post.lefts = pre.lefts - (penult -> oldnode)
						post.rights = pre.rights
       				}

					oldnode.num > penult.num implies {
        		 		post.lefts = pre.lefts 
						post.rights = pre.rights - (penult -> oldnode)
					}
				}
		}
	}
}

pred testremove {
	some r: RemoveNode | {
		isBSTree[r.pre]
    	r.pre != r.post
    	some r.pre.nodes
	}
}
run testremove for exactly 2 Node, 4 seq, exactly 1 RemoveNode, 0 AddNode, 1 Descent, 2 Tree

assert removepreserves {
	all r: RemoveNode | {
    isBSTree[r.pre] implies isBSTree[r.post]
  }
}
// **** Oops: Make sure to give long-enough sequences to actually reach the
// leaf node we need to add to. Failing to do that will make the property fail.
check removepreserves for 2 Tree, 1 RemoveNode, 0 AddNode, 1 Descent, 5 seq, 4 int, 5 Node

