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


//Contract Frame
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
	//Alteration
	if prev+1 == |q| {next:=|q|;}
	//Following Assignment
	else if q[prev+1] == key {next:=IterateRight(q,key,prev+1);}
	else {next:=prev+1;}
}

//Sequential Composition
method FindInitialRight(q:seq<int>, key:int, seed:nat)returns(right:nat)
	requires Sorted(q)
	requires |q| > 0
	requires 0<=seed<|q|
	requires q[seed] == key
	ensures seed < right <= |q| ==> q[right-1]==key
	ensures right < |q| ==> q[right] > key
	ensures right<=|q|
{
	//Alteration
	if |q| == 1 || seed == |q| - 1{right:=|q|;}
	// Following Assignment
	else{right:=IterateRight(q,key,seed);}
}

//Sequential Composition
method FindInitialLeft(q:seq<int>, key:int, seed:nat)returns(left:nat)
	requires Sorted(q)
	requires |q| > 0
	requires 0<=seed<|q|
	requires q[seed] == key
	ensures Left(q,left,key)
	ensures left>0 ==> q[left-1]< key;
{
	//Alteration
	if seed == 0 {left:=0;}
	//Following Assignment
	else{	left:=IterateLeft(q,key,seed);}
}

//Contract Frame
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
	//Alteration
	if prev-1 == 0 {
		if q[prev-1] == key{next:=0;}
		else {next:=1;}
	}
	//Following Assignment
	else if q[prev-1] == key {next:=IterateLeft(q,key,prev-1);}
	else {next:=prev;}
}


method FindRange(q: seq<int>, key: int) returns (left: nat, right: nat)
	requires Sorted(q)
	ensures left <= right <= |q|
	ensures forall i :: 0 <= i < left ==> q[i] < key
	ensures forall i :: right <= i < |q| ==> q[i] > key
	ensures forall i :: left <= i < right ==> q[i] == key
  {
		// Alternation
		if |q| == 0 || key < q[0] {left:=0;right:=0;}
		else if q[|q| - 1] < key {left:=|q|;right:=|q|;}
		else if |q| == 1 {
			// Alternation
			if q[0] == key {left:=0;right:=|q|;}
			else {left:=0;right:=0;}
		}
		else{
			// Weaken Precondition
			left,right:= FindRangeInNotTrivialSeq(q,key);
		}
	}

method FindRangeInNotTrivialSeq(q:seq<int>, key:int) returns(left:nat, right:nat)
	requires Sorted(q)
	requires |q| > 1
	requires q[|q|-1]>=key
	requires q[0]<=key
	ensures left <= right <= |q|
	ensures forall i :: 0 <= i < left ==> q[i] < key
	ensures forall i :: right <= i < |q| ==> q[i] > key
	ensures forall i :: left <= i < right ==> q[i] == key
{
		if q[0] == key {left:=0;right:=FindInitialRight(q,key, 0);}
		else if q[|q|-1] == key {right:=|q|;left:=FindInitialLeft(q,key, |q|-1);}
		else{
			// Introduce Local Variable
			var mid: int := BinarySearch(q, key);
			// Alternation
			if mid < |q| && q[mid] == key{
				// Sequential Composition
				right := FindInitialRight(q,key, mid);
				// Sequential Composition
				left := FindInitialLeft(q,key, mid);
			}
			else {
				assert key !in q;
				right:= mid;
				left:=mid;
			}
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


method BinarySearch(q: seq<int>, key: int) returns (mid: nat)
  requires Sorted(q)
	requires |q| > 1
	requires q[0] < key
	requires q[|q|-1] > key
	ensures key in q ==> 0<=mid<|q|
	ensures key in q ==> q[mid] == key
	ensures key !in q ==> 0<=mid<=|q|
	ensures key !in q && 0<=mid<|q| ==> q[mid] > key
	ensures key !in q && 0<=mid-1<|q| ==> q[mid - 1] < key
{
  var lo, hi := 0, |q|;
	//Iteration
  while lo < hi
    invariant 0 <= lo <= hi <= |q|
    invariant key !in q[..lo] && key !in q[hi..]
  {
    mid := (lo + hi) / 2;
		//Alteration
    if key < q[mid] {
      hi := mid;
    } else if q[mid] < key{
      lo := mid + 1;
    } else {
			assert key in q;
			return mid;
    }
  }
	assert key !in q;
	assert lo >= hi;
	assert hi >= 0;
	

	// Sequential Composition
	if lo >= |q| {lo:=|q| - 1;}
	else if lo == 0 {lo:=1;}
	var seed:nat;

	assert 0<lo<|q|;
	if q[lo] > key {seed:=lo;}
	else if lo+1<|q| && q[lo+1] > key {seed:=lo+1;}
	else if lo + 2 < |q| && q[lo+2] > key {seed:=lo+2;}
	else {seed:=|q|-1;}

	mid := FindNearestBiggest(q,key,seed);

}

//Contract Frame
method FindNearestBiggest(q:seq<int>,key:int,seed:nat)returns(mid:nat)
requires key !in q
requires 0<seed<|q|
requires q[0] < key
requires q[|q| - 1] > key
requires q[seed] > key
ensures 0<mid<|q|
ensures q[mid] > key
ensures q[mid-1] < key
{
	mid:=seed;
	assert q[mid] > key;
	if seed - 1 == 0 {mid:=seed;}
	else if q[seed - 1] > key {mid:=FindNearestBiggest(q,key,seed - 1);}
	else { mid:=seed;}
}


