method Main()
{
	var q := [1,2,2,5,10,10,10,23];
	assert Sorted(q);
	assert 10 in q;
	var i,j := FindRange(q, 10);
	if i<=j {
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
	ensures left<=right ==> left <= right <= |q|
	ensures left<=right ==> forall i :: 0 <= i < left ==> q[i] < key
	ensures left<=right ==> forall i :: right <= i < |q| ==> q[i] > key
	ensures left<=right ==> forall i :: left <= i < right ==> q[i] == key
  {
		left:=|q|;
		right:=0;
		if |q| == 0 {left:=0;right:=0;}
		else{
				var r: int := BinarySearch(q, key);
				if r<0{
					left:=|q|+1;right:=|q|;
				}
				else{
					right := FindInitialRight(q,key, r);
					left := FindInitialLeft(q,key, r);
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