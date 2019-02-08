// include "CCPR191-HeapSort-complete-30Dec18.dfy"

method {:verify true} Parent(index: nat) returns (p: int) 
	ensures p == (index - 1) / 2
{
	p := (index - 1) / 2;
}
function {:verify true} ParentFunc(index: nat) : int 
{
	(index - 1) / 2
}
predicate AncestorIndex(i: nat, j: nat) decreases j-i 
{ 
	i == j || (j > 2*i && ((AncestorIndex(2*i+1, j) || AncestorIndex(2*i+2, j))))
}
// definition of a heap for the prefix q[..length]
predicate hp(q: seq<int>, length: nat)
	requires length <= |q|
{
	forall i,j :: 0 <= i < length && 0 <= j < length && AncestorIndex(i, j) ==> q[i] >= q[j]
}
// a partial heap, restricted for elements whose index is in the given set
predicate ph(q: seq<int>, s: set<nat>)
	requires (forall e :: e in s ==> e < |q|)
{
	forall i,j :: i in s && j in s && AncestorIndex(i, j) ==> q[i] >= q[j]
}
// element k is a valid heap element (in the given range) with respect to its ancestors (lower indices)
predicate lo(q: seq<int>, l: nat, h: nat, k: nat)
	requires l <= h <= |q| && k < |q|
{
	forall i :: l <= i < h && AncestorIndex(i, k) ==> q[i] >= q[k]
}
// element k is a valid heap element (in the given range) with respect to its descendents (higher indices)
predicate hi(q: seq<int>, l: nat, h: nat, k: nat)
	requires l <= h <= |q| && k < |q|
{
	forall j :: l <= j < h && AncestorIndex(k, j) ==> q[k] >= q[j]
}
// the suffix q[i..] holds elements in their final (sorted) positions
//fn
function IndexSet(start: nat, end: nat, except: nat): set<nat> {
	 set i: nat | start <= i < end && i != except }

method {:verify false} swap (a: array<int>, heapsize: nat, x: int, current: nat, parentIndex: int, oldA: seq<int>) 
	requires 0 <= current < a.Length && 0 < heapsize <= a.Length && 0 <= parentIndex < a.Length
	requires Guard1(a,current,parentIndex) && WhileInv(a[..],heapsize,x,current,parentIndex,oldA)
	ensures current > 0 && WhileInv(a[..],heapsize,x,current,parentIndex,oldA)
	modifies a
{
	Lemma3(a,heapsize,x,current,parentIndex,oldA);
	a[current], a[parentIndex] := a[parentIndex], a[current];
}

method {:verify true} HeapInsert(a: array<int>, heapsize: nat, x: int)
	requires 0 <= heapsize < a.Length
	requires hp(a[..], heapsize)
	ensures hp(a[..], heapsize+1)
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
	modifies a
{
	// BottomInsertLemma(a ,heapsize, x);
	var newHeapsize := BottomInsert(a, heapsize, x);
	HeapInsert1(a, newHeapsize, x);	
}
method {:verify true} BottomInsert(a: array<int>, heapsize0: nat, x: int) returns (heapsize: nat)
	requires 0 <= heapsize0 < a.Length
	requires hp(a[..], heapsize0)
	ensures heapsize0 < heapsize && heapsize <= a.Length
	ensures multiset(a[..heapsize]) == multiset(old(a[..heapsize - 1])+[x])
	ensures a[heapsize-1] == x && 0 < heapsize <= a.Length
	ensures hp(a[..], heapsize-1) && ph(a[..heapsize], IndexSet(0, heapsize, heapsize-1))
	modifies a
{
	// Lemma1(a, heapsize0+1, x);
	a[heapsize0] := x;
	heapsize := heapsize0 + 1;
}

// lemma Lemma1 (a: array<int>, heapsize: nat, x: int)
// 	requires 0 <= heapsize - 1  < a.Length
// 	requires hp(a[..], heapsize - 1)

// {}

method {:verify true} HeapInsert1(a: array<int>, heapsize: nat, x: int)
	requires 0 < heapsize <= a.Length && a[heapsize-1] == x
	requires multiset(a[..heapsize]) == multiset(a[..heapsize-1]+[x])
	requires hp(a[..], heapsize-1) && ph(a[..heapsize], IndexSet(0, heapsize, heapsize-1))
	ensures hp(a[..], heapsize) 
	ensures multiset(a[..heapsize]) == multiset(old(a[..heapsize]))
	modifies a
{
	var current, parentIndex := InitCurrAndP(a,heapsize, x);
	Heapify(a, heapsize, x, current, parentIndex);
}

method {:verify true} InitCurrAndP(a: array<int>, heapsize: nat, x: int) returns(current: nat, parentIndex: int)
	requires 0 < heapsize <= a.Length && a[heapsize-1] == x
	requires multiset(a[..heapsize]) == multiset(a[..heapsize-1]+[x])
	requires hp(a[..], heapsize-1)
	ensures 0 <= current < a.Length && current == heapsize - 1 && parentIndex == (current - 1) / 2
	{
	current := InitCurr(a, heapsize, x);
	parentIndex := InitParent(a, heapsize, x, current);
}

method {:verify true} InitCurr(a: array<int>, heapsize: nat, x: int) returns(current: nat)
	requires 0 < heapsize <= a.Length && a[heapsize-1] == x
	requires multiset(a[..heapsize]) == multiset(a[..heapsize-1]+[x])
	requires hp(a[..], heapsize-1)
	ensures 0 <= current < a.Length && current == heapsize - 1
	{
	LemmaCurr(a, heapsize, x);
	current := heapsize - 1; 
}
lemma LemmaCurr (a: array<int>, heapsize: nat, x: int)
	requires 0 < heapsize <= a.Length && a[heapsize-1] == x
	requires multiset(a[..heapsize]) == multiset(a[..heapsize-1]+[x])
	requires hp(a[..], heapsize-1)
	ensures 0 <= heapsize - 1 < a.Length && heapsize - 1 == heapsize - 1
{}

method {:verify true} InitParent(a: array<int>, heapsize: nat, x: int, current: nat) returns(parent: int)
	requires 0 < heapsize <= a.Length && a[heapsize-1] == x
	requires multiset(a[..heapsize]) == multiset(a[..heapsize-1]+[x])
	requires hp(a[..], heapsize-1) && 0 <= current < a.Length
	ensures parent == (current - 1) / 2
{
	LemmaParent(a, heapsize, x, current);
	parent := Parent(current);
}
lemma LemmaParent (a: array<int>, heapsize: nat, x: int, current: nat)
	requires 0 < heapsize <= a.Length && a[heapsize-1] == x
	requires multiset(a[..heapsize]) == multiset(a[..heapsize-1]+[x])
	requires hp(a[..], heapsize-1) && 0 <= current < a.Length
	ensures ParentFunc(current) == (current - 1) / 2
{}

method {:verify true} Heapify(a: array<int>, heapsize: nat, x: int, current0: nat, parentIndex0: int)
	requires 0 <= current0 < a.Length && current0 == heapsize - 1 && parentIndex0 == (current0 - 1) / 2
	requires 0 < heapsize <= a.Length && a[heapsize-1] == x
	requires multiset(a[..heapsize]) == multiset(a[..heapsize-1]+[x])
	requires hp(a[..], heapsize-1) && ph(a[..heapsize], IndexSet(0, heapsize, current0))
	ensures hp(a[..], heapsize)
	ensures multiset(a[..heapsize]) == multiset(old(a[..heapsize]))
	modifies a
{
	var current, parentIndex := current0, parentIndex0; 
	while (Guard1(a, current, parentIndex))
		invariant WhileInv(a[..], heapsize, x, current, parentIndex, old(a[..heapsize]))
		decreases current
	{ 
		current, parentIndex := LoopBody(a, heapsize, x, current, parentIndex, old(a[..heapsize]));	
	}
	// WhileInv && !Guard1
}
predicate method Guard1(a: array<int>, current: nat, parentIndex: int)
	requires 0 <= current < a.Length && parentIndex == (current - 1) / 2
	reads a
{
	current > 0 && a[current] > a[parentIndex]
}
predicate WhileInv(a: seq<int>, heapsize: nat, x:int, current: nat,parentIndex: int, oldA: seq<int>)
	requires 0 <= current < |a|
	requires 0 < heapsize <= |a|
{
	multiset(a[..heapsize]) == multiset(oldA[..]) &&
	ph(a[..], IndexSet(0, heapsize, current))
}


method {:verify true} LoopBody(a: array<int>, heapsize: nat, x: int, current0: nat, parentIndex0: int, oldA: seq<int>) returns (current: nat, parentIndex: int)
	requires 0 <= current0 < a.Length && 0 < heapsize <= a.Length && 0 <= parentIndex0 < a.Length
	requires Guard1(a,current0,parentIndex0) && WhileInv(a[..],heapsize,x,current0,parentIndex0,oldA)
	ensures WhileInv(a[..], heapsize, x, current, parentIndex, oldA)
	modifies a
{
	swap(a, heapsize, x, current0, parentIndex0, oldA); 
	current, parentIndex := LoopBody1(a,heapsize,x,current0,parentIndex0);
	// current := parentIndex; 
	// parentIndex := Parent(current);
}

lemma {:verify true} Lemma3(a: array<int>, heapsize: nat, x: int, current: nat, parentIndex: int, oldA: seq<int>) 
	requires 0 <= current < a.Length && 0 < heapsize <= a.Length && 0 <= parentIndex < a.Length
	requires Guard1(a,current,parentIndex) && WhileInv(a[..],heapsize,x,current,parentIndex,oldA)
	ensures current > 0 && WhileInv(a[..parentIndex] + [a[parentIndex]] + a[parentIndex+1..current] + [a[current]],heapsize,x,parentIndex,current,oldA)
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
