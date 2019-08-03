datatype Tree = Empty | Node(int,Tree,Tree)

method Main() {
	var tree := Node(5, Node(2, Empty, Empty), Node(8, Node(7, Empty, Empty), Node(8, Empty, Empty)));
	assert NumbersInTree(tree) == multiset([2,5,7,8,8]);
	assert NumbersInTree(tree)[2] == 1; // the number 2 occurs once in the tree
	assert NumbersInTree(tree)[5] == 1; // the number 5 occurs once in the tree
	assert NumbersInTree(tree)[7] == 1; // the number 7 occurs once in the tree
	assert NumbersInTree(tree)[8] == 2; // the number 8 occurs twice in the tree
	assert NumbersInTree(tree)[9] == 0; // the number 9 does not occur in the tree
	assert BST(tree);
	var count8 := CountOccurrences(tree, 8);
	print "The number of occurrences of 8 in the tree ";
	print tree;
	print " is ";
	print count8;
	assert count8 == 2;
}

function NumbersInTree(t: Tree): multiset<int>
decreases t
{
	match t {
		case Empty => multiset([])
		case Node(n,l,r) => multiset([n])+NumbersInTree(l)+NumbersInTree(r)
	}
}

// a possible definition for a binary search tree:
predicate BST(t: Tree)
decreases t
{
	match t {
		case Empty => true
		case Node(n,l,r) =>
			BST(l) && BST(r) &&
			(forall x :: x in NumbersInTree(l) ==> x < n) &&
			(forall x :: x in NumbersInTree(r) ==> x >= n)
	}
}

method CountOccurrences(t: Tree, key: int) returns (count: nat)
	requires BST(t)
	ensures count == NumbersInTree(t)[key]
  {
		count := RecEffective(t, key);
  }

lemma LCountingTree(root: Tree, val: int, key:int, left: Tree, right: Tree, leftAcc: nat, rightAcc: nat)
	requires rightAcc == NumbersInTree(right)[key] 
	requires leftAcc == NumbersInTree(left)[key] 
	requires  root == Node(val,left,right) 
	ensures (if val == key then 1 else 0) + leftAcc + rightAcc == NumbersInTree(root)[key]
{
	calc {
		NumbersInTree(root)[key];
	== { assert root == Node(val,left,right); } 
		(if val == key then 1 else 0) + NumbersInTree(left)[key] + NumbersInTree(right)[key];
	== 
		(if val == key then 1 else 0) + leftAcc + rightAcc;
	}
}

method RecEffective(tree: Tree, key: int) returns (count: nat)
	requires BST(tree)
	decreases tree
	ensures count == NumbersInTree(tree)[key]
  {
  var leftAcc := 0;
  var rightAcc := 0;
	match tree {
	case Empty =>
		assert tree == Empty;
		// ==>
		assert 0 == NumbersInTree(tree)[key];
		count := 0;
		assert count == NumbersInTree(tree)[key];
	case Node(val,left,right) =>
		assert tree == Node(val,left,right);
		assert left < tree;
		assert right < tree;
    if key < val{
      leftAcc := RecEffective(left, key);
    }else{
			rightAcc:= RecEffective(right, key);
    }
		LCountingTree(tree, val, key, left, right, leftAcc, rightAcc); 
		assert (if val == key then 1 else 0) +  leftAcc + rightAcc == NumbersInTree(tree)[key];
    count := (if val == key then 1 else 0) +  leftAcc + rightAcc;
		assert count == NumbersInTree(tree)[key];
	}
	assert count == NumbersInTree(tree)[key];
}