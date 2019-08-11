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

method FindLeft(q:seq<int>, key:int, seed:nat)returns(left:nat)
	requires Sorted(q)
	decreases seed
	requires |q| > 0
	requires 0 <= seed < |q|
	ensures left <= seed
	ensures forall i :: 0 <= i < left ==> q[i] < key
{
	if seed == 0 {left:=0;}
	else if q[seed] < key {left:=seed;}
	else {left := FindLeft(q, key, seed - 1);}
}



method FindRight(q:seq<int>, key:int, seed:nat)returns(right:nat)
	requires Sorted(q)
	requires |q| > 0
	requires 0<seed<|q|
	requires q[seed] == key
	ensures seed<=right
	ensures right+1<|q| ==> q[right + 1] > key
{
right:=seed;
while right<|q| && q[right] == key{
	right := right+1;
}
}

method FindInitialRight(q:seq<int>, key:int, seed:nat)returns(right:nat)
	requires Sorted(q)
	requires |q| > 0
	requires 0<=seed<|q|
	requires q[seed] == key
	ensures 0<right<=|q|
	ensures q[right-1]==key
	ensures forall i :: right <= i < |q| ==> q[i] > key
{
	if |q| == 1{right:=1;}
	else if seed == |q| - 1 {right:=|q|;}
	else if seed == 0{
		if q[seed+1]!=key {right:=1;}
		else {right:=FindRight(q,key,seed+1);right:=right+1;}
	}
	else{
		right:=FindRight(q,key,seed);right:=right+1;
	}
	// if |q| == 1 {right:=1;}
	// else {
	// 		if seed > 0 {
	// 			right:=FindRight(q,key,seed);
	// 			right:=right+1;
	// 		}
	// 		else{
	// 			if q[seed+1] == key{
	// 				right:=FindRight(q,key,seed+1);
	// 				right:=right+1;
	// 			}
	// 			else{
	// 				right:=1;
	// 			}
	// 		}
	// 	}
}

method FindInitialLeft(q:seq<int>, key:int, seed:nat)returns(left:nat)
	requires |q| > 0
	requires 0<=seed<|q|
	requires q[seed] == key
	ensures 0<=left<|q|
	ensures q[left]==key
	ensures forall i :: 0 <= i < left ==> q[i] < key
{

}

method FindRange(q: seq<int>, key: int) returns (left: nat, right: nat)
	requires Sorted(q)
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
				assume 0<=r<|q|;// if value is not exists in the array we cannot find range;
				assert q[r] == key;
				right := FindInitialRight(q,key,r);
				left := FindInitialLeft(q,key,r);
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


method BinarySearch(a: seq<int>, key: int) returns (r: int)
  requires Sorted(a)
  ensures 0 <= r ==> r < |a| && a[r] == key
{
  var lo, hi := 0, |a|;
  while lo < hi
    invariant 0 <= lo <= hi <= |a|
    invariant key !in a[..lo] && key !in a[hi..]
  {
    var mid := (lo + hi) / 2;
    if key < a[mid] {
      hi := mid;
    } else if a[mid] < key {
      lo := mid + 1;
    } else {
      return mid;
    }
  }
  return -1;
}