// Feb 29

abstract sig Node {}
sig Empty extends Node {}
sig Data extends Node {
	num: Int,
	left: Node,
  right: Node
}

pred btree {
	// root reaches everything
  some r: Node |
		Node in r.^(left + right) + r

  all n: Node | {
	  // no cycles
		n not in n.^(left+right) 
    // at most one parent for each node
		lone n.~(left+right)
    
    // distinct children if any
		//n.left != n.right // fails if using no left/right instead of Empty (Wed)
    no n.left & n.right
  }
}

run btree for exactly 3 Data, 4 Empty

pred orderedtree {
	btree

   // * is REFLEXIVE transitive closure 
  all n: Node, n': n.left.*(left+right) - Empty | {
    n.num > n'.num
  }

  all n: Node, n': n.right.*(left+right) - Empty | {
    n.num < n'.num
  }
}

run orderedtree for exactly 7 Node

-------------------------

// A descent is a search path down the tree. 
// Model in a way similar to how we'd implement the search
lone sig Descent {
  val: Int,
  path: seq Node
} {
  // start at root
  no path[0].~(left+right)
  // actually do something
  not path.isEmpty

  // search until done
  path.last in Empty or path.last.num = val
  path.last in Empty implies val not in path.elems.num

  // ? do we need this?
  all idx: path.inds - path.lastIdx |
		path[idx].num != val

  // move down in correct direction
  all idx: path.inds - path.lastIdx | {
    let idx' = add[idx, 1] | {
      path[idx].num > val implies path[idx'] = path[idx].left
	    path[idx].num < val implies path[idx'] = path[idx].right
    }
  }  
}

run orderedtree for exactly 1 Descent, exactly 7 Node

// A descent models a search path through the tree.
// Check to make sure that searching binary trees works!
assert findifthere {
	all d: Descent |
		orderedtree implies {
			(d.val in Node.num =>
       d.path.last.num = d.val else
       d.path.last.num != d.val
      )
    }
}

// If this succeeds, any implementation that matches our Descent spec
// will work (on small trees, anyway)
check findifthere for exactly 1 Descent, exactly 7 Node
