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
{
	match t {
		case Empty => multiset([])
		case Node(n,l,r) => multiset([n])+NumbersInTree(l)+NumbersInTree(r)
	}
}

// a possible definition for a binary search tree:
predicate BST(t: Tree)
{
	match t {
		case Empty => true
		case Node(n,l,r) =>
			BST(l) && BST(r) &&
			(forall x :: x in NumbersInTree(l) ==> x < n) &&
			(forall x :: x in NumbersInTree(r) ==> x >= n)
	}
}

function TreeSize(nt: Tree): nat
{
	match nt {
		case Empty => 1
		case Node(n',nt1,nt2) => 1+TreeSize(nt1)+TreeSize(nt2)
	}
}

function ForestSize(ntl: seq<Tree>): nat
{
	if ntl == [] then 0 else TreeSize(ntl[0]) + ForestSize(ntl[1..])
}

function OccurencesForest(ntl: seq<Tree>, key:int): nat
{
	if ntl == [] then 0 else NumbersInTree(ntl[0])[key] + OccurencesForest(ntl[1..], key)
}

method CountOccurrences(t: Tree, key: int) returns (count: nat)
	requires BST(t)
	ensures count == NumbersInTree(t)[key]
  {
    var ntl := [t];
    count := 0;
    while ntl != []
      invariant count == NumbersInTree(t)[key] - OccurencesForest(ntl, key)
      decreases ForestSize(ntl)
      {
        ghost var V0 := ForestSize(ntl);
        var nt;
        // pop
        nt, ntl := ntl[0], ntl[1..];
        match nt {
        case Empty =>
          // skip
        case Node(n', nt1, nt2) =>
          if n' == key { 
            count := count + 1;          
            }
          ntl := [nt1, nt2] + ntl;
        }
        assert ForestSize(ntl) < V0;
      }
      	assert ntl == [];
        assert count == NumbersInTree(t)[key] - OccurencesForest(ntl, key);
        // ==>
        assert count == NumbersInTree(t)[key];
  }

lemma L1(nt: Tree, n': int, key:int, nt1: Tree, nt2: Tree, occurrences1: nat, occurrences2: nat)
	requires occurrences2 == NumbersInTree(nt2)[key] // pre0
	requires occurrences1 == NumbersInTree(nt1)[key] // pre1
	requires  nt == Node(n',nt1,nt2) // pre2
	ensures (if n' == key then 1 else 0) + occurrences1 + occurrences2 == NumbersInTree(nt)[key]
{
	calc {
		NumbersInTree(nt)[key];
	== { assert nt == Node(n',nt1,nt2); } // pre2 and the definition of SumTree for Node
		(if n' == key then 1 else 0) + NumbersInTree(nt1)[key] + NumbersInTree(nt2)[key];
	== // pre0 and pre1
		(if n' == key then 1 else 0) + occurrences1 + occurrences2;
	}
}

method RecCountOccurrences(t: Tree, key: int) returns (count: nat)
	requires BST(t)
	ensures count == NumbersInTree(t)[key]
  {
	match t {
	case Empty =>
		assert t == Empty;
		// ==>
		assert 0 == NumbersInTree(t)[key];
		count := 0;
		assert count == NumbersInTree(t)[key];
	case Node(n',nt1,nt2) =>
		assert t == Node(n',nt1,nt2);
		assert nt1 < t; // for termination
		var sum1 := CountOccurrences(nt1, key);
		assert sum1 == NumbersInTree(nt1)[key];
		assert nt2 < t; // for termination
		var sum2 := CountOccurrences(nt2, key);
		assert sum2 == NumbersInTree(nt2)[key];
		assert sum1 == NumbersInTree(nt1)[key]; 
		assert t == Node(n',nt1,nt2); 
		L1(t, n', key, nt1, nt2, sum1, sum2); 
		assert (if n' == key then 1 else 0) + sum1 + sum2 == NumbersInTree(t)[key];
    count := (if n' == key then 1 else 0) + sum1 + sum2;
		assert count == NumbersInTree(t)[key];
	}
	assert count == NumbersInTree(t)[key];
}