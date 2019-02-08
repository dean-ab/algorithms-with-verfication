// include "CCPR191-HeapSort-complete-30Dec18.dfy"

method {:verify false} parent(index: nat) returns (p: int) 
{
	p := (index - 1) / 2;
}
predicate AncestorIndex(i: nat, j: nat) decreases j-i 
{ 
	i == j || (j > 2*i && ((AncestorIndex(2*i+1, j) || AncestorIndex(2*i+2, j))))
}

predicate hp(q: seq<int>, length: nat)
	requires length <= |q|
{
	forall i,j :: 0 <= i < length && 0 <= j < length && AncestorIndex(i, j) ==> q[i] >= q[j]
}

method {:verify false} swap (heap: array<int>, x: nat, y: nat) 
	modifies heap
{
	var temp := heap[x];
	heap[x] := heap[y];
	heap[y] := temp;
}

method {:verify true} HeapInsert(a: array<int>, heapsize: nat, x: int)
	requires heapsize < a.Length
	requires hp(a[..], heapsize)
	ensures hp(a[..], heapsize+1)
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
	modifies a
{
	// BottomInsertLemma(a ,heapsize, x);
	var newHeapsize := BottomInsert(a, heapsize, x);
	HeapInsert1(a, newHeapsize, x, old(a[..heapsize]));	
}
method {:verify true} BottomInsert(a: array<int>, heapsize0: nat, x: int) returns (heapsize: nat)
	requires heapsize0 < a.Length
	requires hp(a[..], heapsize0)
	ensures heapsize <= a.Length
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
	ensures a[heapsize-1] == x
{
	Lemma1(a, heapsize0+1, x);
	a[heapsize0] := x;
	heapsize := heapsize0 + 1;
}

lemma Lemma1 (a: array<int>, heapsize: nat, x: int)
	requires heapsize-1 < a.Length
	requires hp(a[..], heapsize-1)
	ensures heapsize == heapsize
{}

method {:verify true} HeapInsert1(a: array<int>, heapsize: nat, x: int, ghost oldHeap: seq<int>)
	requires heapsize <= a.Length
	requires hp(a[..], heapsize-1)
	requires a[heapsize-1] == x
	ensures hp(a[..], heapsize)
	ensures multiset(a[..heapsize]) == multiset(oldHeap[..]+[x])
	modifies a
{
	var current := heapsize; 
	var parentIndex := parent(current);
	while (parentIndex >= 0 && a[current] > a[parentIndex]) { 
		swap(a, current, parentIndex); 
		current := parent(current); 
		parentIndex := parent(current);
	}
}


lemma {:verify true} BottomInsertLemma(a: array<int>, heapsize: nat, x: int)
	requires heapsize < a.Length
	requires hp(a[..], heapsize)
	
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
{}

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
