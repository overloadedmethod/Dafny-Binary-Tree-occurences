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
  decreases t
  {
    count := CountOccurrences'(t,key);
  }

  method CountOccurrences'(t: Tree, key: int) returns (count: nat)
	requires BST(t)
	ensures count == NumbersInTree(t)[key]
  decreases t, 3
  {
    	// alternation
      match t {
        case Empty =>
          count := CountOccurrencesTree1a(t, key);
        case Node(n1, nt1, nt2) =>
          assert t == t && 2 < 3;
          count := CountOccurrencesTree1b(t, n1, nt1, nt2, key);
      }
  }

  method CountOccurrences''(t: Tree, key: int) returns (count: nat)
	requires BST(t)
	ensures count == NumbersInTree(t)[key]
  decreases t, 3
  {
    	// alternation
      match t {
        case Empty =>
          count := CountOccurrencesTree1a(t, key);
        case Node(n1, nt1, nt2) =>
          assert t == t && 2 < 3;
          count := CountOccurrencesTree1b(t, n1, nt1, nt2, key);
      }
  }


method CountOccurrencesTree1a(t: Tree, key:int) returns (count: nat)
	requires BST(t)
	requires t == Empty
	ensures count == NumbersInTree(t)[key]
{
	// assignment
	Lemma1a(t, key);
	count := 0;
}

lemma Lemma1a(t: Tree, key:int)
	requires t == Empty
	ensures 0 == NumbersInTree(t)[key]
{}

method CountOccurrencesTree1b(t: Tree, n1: int, nt1: Tree, nt2: Tree, key:int) returns (count: nat)
	requires BST(t)
	requires t == Node(n1, nt1, nt2)
	ensures count == NumbersInTree(t)[key]
	decreases t, 2
{
	// following assignment
	assert t == t && 1 < 2;
	count := CountOccurrencesTree2(t, n1, nt1, nt2, key);
}

method CountOccurrencesTree2(t: Tree, n1: int, nt1: Tree, nt2: Tree, key:int) returns (count: nat)
	requires BST(t)
	requires t == Node(n1, nt1, nt2)
	ensures count == NumbersInTree(t)[key]
	decreases t, 1
{
	// introduce local variable + following assignment + sequential composition + contract frame*2
	var tmp1, tmp2;
  assert t == t && 0 < 1;
  if key < n1{
    tmp1 := CountOccurrencesTree3a(t, n1, nt1, nt2, key);
  }else{
    tmp1:= 0;
  }
  if n1 == key {tmp1:=tmp1+1;}
  tmp2 := CountOccurrencesTree3b(t, n1, nt1, nt2, tmp1, key);
	count := tmp1+tmp2;
}

method CountOccurrencesTree3a(nt: Tree, n1: int, nt1: Tree, nt2: Tree, key:int) returns (tmp1: nat)
	requires BST(nt)
	requires nt == Node(n1, nt1, nt2)
	ensures tmp1 == NumbersInTree(nt1)[key] && nt == Node(n1, nt1, nt2)
	decreases nt, 0
{
	// recursive call (+ strengthen postcondition)
	assert nt1 < nt; // structureal order
	tmp1 := CountOccurrences(nt1, key);
	Lemma3a(nt, n1, nt1, nt2, tmp1, key);
}

lemma Lemma3a(t: Tree, n1: int, nt1: Tree, nt2: Tree, tmp1: nat, key:int)
	requires tmp1 == NumbersInTree(nt1)[key]
	requires t == Node(n1, nt1, nt2) // from the precondition of ComputeSumTree3a (all variables are not in the frame)
	ensures tmp1 == NumbersInTree(nt1)[key] && t == Node(n1, nt1, nt2)
{}

method CountOccurrencesTree3b(nt: Tree, n1: int, nt1: Tree, nt2: Tree, tmp1: nat, key:int) returns (tmp2: nat)
	requires BST(nt)
	requires tmp1 == NumbersInTree(nt1)[key] + (if n1 == key then 1 else 0) && nt == Node(n1, nt1, nt2)
	ensures tmp1+tmp2 == NumbersInTree(nt)[key]
	decreases nt, 0
{
	// recursive call (+ strengthen postcondition)
	assert nt2 < nt; // structureal order
	tmp2 := CountOccurrences(nt2, key);
	Lemma3b(nt, n1, nt1, nt2, tmp1, tmp2, key);
}

lemma Lemma3b(nt: Tree, n1: int, nt1: Tree, nt2: Tree, tmp1: nat, tmp2: nat, key:int)
	requires tmp2 == NumbersInTree(nt2)[key]
	requires tmp1 == NumbersInTree(nt1)[key] + (if n1 == key then 1 else 0)  && nt == Node(n1, nt1, nt2)
	ensures tmp1+tmp2 == NumbersInTree(nt)[key]
{}
