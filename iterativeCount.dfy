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


// TODO: perform a stepwise-refinement of this specification into iterative or recursive executable code;
// you should document each step fully, stating the name of the applied law, the specification of called methods
// (that will act as a starting point for further steps), and lemma specifications
// (for documenting the proof obligations), where needed;
// you should submit the program in a form that compiles with no errors (in Dafny 2.2.0) and generates an executable file;
// trivially-correct unproved lemmas may still be awarded full points; please leave them with an empty body ("{}"),
// a "{:verify false}" annotation (to allow the generation of an executable file), and a short verbal justification.
// DO NOT CHANGE THE SPECIFICATION of predicate "BST", of function "NumbersInTree", or of method "CountOccurrences"
// (except for adding a "decreases" clause in case of a recursive solution);
// unusual code made of complex expressions (such as "forall","exists","in","!in") or with "such that" assignment statements (":|") is NOT ACCEPTABLE;
// DO NOT USE multisets in the executable code!
// at most 10% of the grade will be dedicated to the efficiency and worst-case time complexity of your algorithm.