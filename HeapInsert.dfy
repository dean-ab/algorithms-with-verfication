include "CCPR191-HeapSort-complete-30Dec18.dfy"

method {:verify false} parent(index: nat) returns (p: nat) {
	p := (index - 1) / 2;
}

method {:verify false} swap (heap: array<int>, x: nat, y: nat) 
	modifies heap
{
	var temp := heap[x];
	heap[x] := heap[y];
	heap[y] := temp;
}


method {:verify false} HeapInsert(a: array<int>, heapsize: nat, x: int)
	requires heapsize < a.Length
	requires hp(a[..], heapsize)
	ensures hp(a[..], heapsize+1)
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
	modifies a
{

	a[heapsize] := x; 
  
	// Traverse up and fix violated property 
	var current := heapsize; 
	var parentIndex := parent(current);
	while (a[current] > a[parentIndex]) { 
		swap(a, current, parentIndex); 
		current := parent(current); 
	}
}

method Main() {
	var a := new int[8];
	a[0] := 6;
	a[1] := 4;
	a[2] := 5;
	a[3] := 3;
	a[4] := 2;
	a[5] := 0;
	a[6] := 1;
	HeapInsert(a, 7, 8);
	print a[..];
}