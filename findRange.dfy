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
	ensures left <= right <= |q|
	ensures forall i :: 0 <= i < left ==> q[i] < key
	ensures forall i :: right <= i < |q| ==> q[i] > key
	ensures forall i :: left <= i < right ==> q[i] == key
  {
		if |q| == 0 || key < q[0] {left:=0;right:=0;}
		else if q[|q| - 1] < key {left:=|q|;right:=|q|;}
		else if |q| == 1 {
			if q[0] == key {left:=0;right:=|q|;}
			else {left:=0;right:=0;}
		}
		else{
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
			var mid: int := BinarySearch(q, key);
			if mid < |q| && q[mid] == key{
				right := FindInitialRight(q,key, mid);
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



// method BinarySearch(a: array<int>, key: int) returns (r: int,found:bool)
//   requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
//   ensures 0 <= r ==> r < a.Length && a[r] == key
//   ensures r < 0 ==> key !in a[..]
// {
//   var lo, hi := 0, a.Length;
// 	var mid;
// 	found:=false;
//   while lo < hi && !found
//     invariant 0 <= lo <= hi <= a.Length
//     invariant key !in a[..lo] && key !in a[hi..]
//   {
//     mid := (lo + hi) / 2;
//     if key < a[mid] {
//       hi := mid;
//     } else if a[mid] < key {
//       lo := mid + 1;
//     } else {
// 			found:=true;
//     }
//   }
//   r:=mid;
// }

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
  while lo < hi
    invariant 0 <= lo <= hi <= |q|
    invariant key !in q[..lo] && key !in q[hi..]
  {
    mid := (lo + hi) / 2;
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
	if lo >= |q| {lo:=|q| - 1;}
	
	mid:=lo;
	assert q[mid] > key;
	while mid>0 && q[mid-1]>key{
		mid:=mid-1;
	}
	// assume q[mid] > key;
	

}



// method BinarySearch(q: seq<int>, key: int) returns (mid: nat)
//   requires Sorted(q)
// 	requires |q| > 0
// 	ensures key in q ==> q[mid] == key
// 	ensures key !in q && 0<mid<|q| ==> q[mid - 1] < key
// 	ensures key !in q && 0<mid<|q|-1 ==> q[mid + 1] > key
// {
//   var lo, hi := 0, |q|-1;
//   while lo < hi && hi - lo != 1
//     invariant 0 <= lo <= hi < |q|
//     invariant key !in q[..lo] && key !in q[hi..]
//   {
//     mid := (lo + hi) / 2;
//     if key < q[mid] {
//       hi := mid;
//     } else if q[mid] < key {
//       lo := mid + 1;
//     } else {
// 			return mid;
//     }
//   }
//   return mid;
// }