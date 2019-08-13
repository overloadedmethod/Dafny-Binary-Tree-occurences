method Main()
{
	var q := [1,2,2,5,10,10,10,23];
	assert Sorted(q);
	assert 10 in q;
	var i,j := FindRange(q, 10);
	print "The number of occurrences of 10 in the sorted sequence [1,2,2,5,10,10,10,23] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j-1;
	print ").\n";
	assert i == 4 && j == 7 by {
		assert q[0] <= q[1] <= q[2] <= q[3] < 10;
		assert q[4] == q[5] == q[6] == 10;
		assert 10 < q[7];
	}
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate Left(q:seq<int>, left:nat, key:int){
	0<=left<|q| && q[left] == key
}

method IterateRight(q:seq<int>, key:int,prev:nat)returns(next:nat)
	requires Sorted(q)
	requires |q| > 0
	requires 0<=prev<|q|
	requires q[prev] == key
	ensures q[prev] == key
	ensures next < |q| ==> q[next]>key
	ensures next <= |q| ==> q[next-1] == key
	ensures prev<=next<=|q|
	decreases |q| - prev
{
	if prev+1 == |q| {next:=|q|;}
	else if q[prev+1] == key {next:=IterateRight(q,key,prev+1);}
	else {next:=prev+1;}
}

method FindInitialRight(q:seq<int>, key:int, seed:nat)returns(right:nat)
	requires Sorted(q)
	requires |q| > 0
	requires 0<=seed<|q|
	requires q[seed] == key
	ensures seed < right <= |q| ==> q[right-1]==key
	ensures right < |q| ==> q[right] > key
	ensures right<=|q|
{
	if |q| == 1 || seed == |q| - 1{right:=|q|;}
	else{
		right:=IterateRight(q,key,seed);
	}
}

method FindInitialLeft(q:seq<int>, key:int, seed:nat)returns(left:nat)
	requires Sorted(q)
	requires |q| > 0
	requires 0<=seed<|q|
	requires q[seed] == key
	ensures Left(q,left,key)
	ensures left>0 ==> q[left-1]< key;
{
	if seed == 0 {left:=0;}
	else{	left:=IterateLeft(q,key,seed);}
}

method IterateLeft(q:seq<int>, key:int,prev:nat)returns(next:nat)
	requires Sorted(q)
	requires |q| > 0
	requires 0<prev<|q|
	requires q[prev] == key
	ensures next <= prev
	ensures q[next] == key
	ensures next>0 ==> q[next-1] < key
	decreases prev
{
	if prev-1 == 0 {
		if q[prev-1] == key{next:=0;}
		else {next:=1;}
	}
	else if q[prev-1] == key {next:=IterateLeft(q,key,prev-1);}
	else {next:=prev;}
}


method FindRange(q: seq<int>, key: int) returns (left: nat, right: nat)
	requires Sorted(q)
	requires key in q // without this requirement we cannot ensure that first and fourth expressions will be ensured
	ensures left <= right <= |q|
	ensures forall i :: 0 <= i < left ==> q[i] < key
	ensures forall i :: right <= i < |q| ==> q[i] > key
	ensures forall i :: left <= i < right ==> q[i] == key
  {
		left:=|q|;
		right:=0;
		if |q| == 0 {left:=0;right:=0;}
		else{
			var r: int := BinarySearch(q, key);
			right := FindInitialRight(q,key, r);
			left := FindInitialLeft(q,key, r);
		}
	}

// TODO: perform a stepwise-refinement of this specification into iterative executable code (using loops);
// you should document each step fully, stating the name of the applied law, the specification of called methods
// (that will act as a starting point for further steps), and lemma specifications
// (for documenting the proof obligations), where needed;
// you should submit the program in a form that compiles with no errors (in Dafny 2.2.0) and generates an executable file;
// trivially-correct unproved lemmas may still be awarded full points; please leave them with an empty body ("{}"),
// a "{:verify false}" annotation (to allow the generation of an executable file), and a short verbal justification.
// DO NOT CHANGE THE SPECIFICATION of method "FindRange" or of predicate "Sorted";
// unusual code made of complex expressions (such as "forall","exists","in","!in") or with "such that" assignment statements (":|") is NOT ACCEPTABLE;
// at most 10% of the grade will be dedicated to the efficiency and worst-case time complexity of your algorithm.



predicate Inv(q: seq<int>, key: int, i: nat, j: nat, k: nat)
{
	i < k <= |q| && j == (i+k)/2 && Sorted(q) && key in q[i..k]
}

method BinarySearch(q: seq<int>, key: int) returns (j: nat)
	requires Sorted(q) && key in q
	ensures j < |q| && q[j] == key
{
	// introduce local variable + strengthen postcondition
	var i, k;
	i, j, k := BinarySearch1(q, key);
	LemmaStrngthenPostcondition(q, key, i, j, k);
}

lemma LemmaStrngthenPostcondition(q: seq<int>, key: int, i: nat, j: nat, k: nat)
	requires Inv(q, key, i, j, k) && q[j] == key
	ensures j < |q| && q[j] == key
// recall the definition of Inv:
{}

method BinarySearch1(q: seq<int>, key: int) returns (i: nat, j: nat, k: nat)
	requires Sorted(q) && key in q
	ensures Inv(q, key, i, j, k) && q[j] == key
{
	// leading assignment + weaken precondition
	assert 0 == 0 && |q|/2 == |q|/2 && |q| == |q|;
	i, j, k := 0, |q|/2, |q|;
	assert i == 0 && j == |q|/2 && k == |q|;
	LemmaWeakenPrecondition(q, key, i, j, k);
	i, j, k := BinarySearch2(q, key, i, j, k);
}

lemma LemmaWeakenPrecondition(q: seq<int>, key: int, i: nat, j: nat, k: nat)
	requires Sorted(q) && key in q
	requires i == 0 && j == |q|/2 && k == |q|
	ensures Inv(q, key, i, j, k)
// recall the definition of Inv:
{}

method BinarySearch2(q: seq<int>, key: int, i0: nat, j0: nat, k0: nat) returns (i: nat, j: nat, k: nat)
	requires Inv(q, key, i0, j0, k0)
	ensures Inv(q, key, i, j, k) && q[j] == key
{
	i, j, k := i0, j0, k0;
	// iteration
	while q[j] != key
		invariant Inv(q, key, i, j, k)
		decreases k-i
	{
		i, j, k := BinarySearch3(q, key, i, j, k);
	}
}

method BinarySearch3(q: seq<int>, key: int, i0: nat, j0: nat, k0: nat) returns (i: nat, j: nat, k: nat)
	requires Inv(q, key, i0, j0, k0) && q[j0] != key
	ensures Inv(q, key, i, j, k) && 0 <= k-i < k0-i0
{
	i, j, k := i0, j0, k0;
	// following assignment + contract frame
	i, k := BinarySearch4(q, key, i, j, k);
	j := (i+k)/2;
}

method BinarySearch4(q: seq<int>, key: int, i0: nat, j: nat, k0: nat) returns (i: nat, k: nat)
	requires Inv(q, key, i0, j, k0) && q[j] != key
	ensures Inv(q, key, i, (i+k)/2, k) && 0 <= k-i < k0-i0
{
	i, k := i0, k0;
	// alternation + contract frame(*2)
	if q[j] > key
	{
		k := BinarySearch5a(q, key, i, j, k);
	}
	else
	{
		i := BinarySearch5b(q, key, i, j, k);
	}
}

method BinarySearch5a(q: seq<int>, key: int, i: nat, j: nat, k0: nat) returns (k: nat)
	requires Inv(q, key, i, j, k0) && q[j] > key
	ensures Inv(q, key, i, (i+k)/2, k) && 0 <= k-i < k0-i
{
	// assignment
	Lemma5a(q, key, i, j, k0);
	k := j;
}

lemma Lemma5a(q: seq<int>, key: int, i: nat, j: nat, k: nat)
	requires Inv(q, key, i, j, k) && q[j] > key
	ensures Inv(q, key, i, (i+j)/2, j) && 0 <= j-i < k-i
{}

method BinarySearch5b(q: seq<int>, key: int, i0: nat, j: nat, k: nat) returns (i: nat)
	requires Inv(q, key, i0, j, k) && q[j] < key
	ensures Inv(q, key, i, (i+k)/2, k) && 0 <= k-i < k-i0
{
	// assignment
	Lemma5b(q, key, i0, j, k);
	i := j;
}

lemma Lemma5b(q: seq<int>, key: int, i: nat, j: nat, k: nat)
	requires Inv(q, key, i, j, k) && q[j] < key
	ensures Inv(q, key, j, (j+k)/2, k) && 0 <= k-j < k-i
{}

