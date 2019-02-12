// include "CCPR191-HeapSort-complete-30Dec18.dfy"

method {:verify false} Parent(index: nat) returns (p: int) 
	ensures p == (index - 1) / 2
	ensures p <= index
{
	p := (index - 1) / 2;
}
function {:verify false} ParentFunc(index: nat) : int 
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
predicate ph(q: seq<int>, s: set<nat>, k: nat)
	requires (forall e :: e in s ==> e < |q|)
{
	(forall i,j :: i in s && j in s && AncestorIndex(i, j) ==> q[i] >= q[j]) &&
	forall j :: j in s && AncestorIndex(k, j) ==> q[k] >= q[j]
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

method {:verify false} HeapInsert(a: array<int>, heapsize: nat, x: int)
	requires 0 <= heapsize < a.Length
	requires hp(a[..], heapsize)
	ensures hp(a[..], heapsize+1)
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
	modifies a
{
	// BottomInsertLemma(a ,heapsize, x);
	var newHeapsize := BottomInsert(a, heapsize, x); //add x to a end
	HeapInsert1(a, newHeapsize, x, old(a[..]));	
}
method {:verify false} BottomInsert(a: array<int>, heapsize0: nat, x: int) returns (heapsize: nat)
	requires 0 <= heapsize0 < a.Length
	requires hp(a[..], heapsize0)
	ensures heapsize0 == heapsize-1 && 0 < heapsize <= a.Length
	ensures multiset(a[..heapsize]) == multiset(old(a[..heapsize - 1]+[x]))
	ensures a[heapsize-1] == x && 0 < heapsize <= a.Length
	ensures ph(a[..heapsize], IndexSet(0, heapsize, heapsize-1))
	modifies a
{
	Lemma1(a[..heapsize0]+[x]+a[heapsize0+1..] , heapsize0+1, x, a);
	a[heapsize0] := x;
	heapsize := heapsize0 + 1;
}

lemma Lemma1 (a: seq<int>, heapsize: nat, x: int,oldA: array<int>)
	requires 0 <= heapsize - 1 < |a| == oldA.Length
	requires hp(a[..], heapsize - 1) && a[..] == oldA[..heapsize-1]+[x]+oldA[heapsize..]
	ensures heapsize == heapsize && heapsize <= |a|
	ensures multiset(a[..heapsize]) == multiset(oldA[..heapsize-1]+[x])
	ensures a[heapsize-1] == x && 0 < heapsize <= |a|
	ensures ph(a[..heapsize], IndexSet(0, heapsize, heapsize-1))
{	
}

method {:verify false} HeapInsert1(a: array<int>, heapsize: nat, x: int, ghost oldA: seq<int>)
	requires 0 < heapsize <= a.Length == |oldA| && a[heapsize-1] == x
	requires multiset(a[..heapsize]) == multiset(oldA[..heapsize-1]+[x])
	requires hp(a[..], heapsize-1) && ph(a[..heapsize], IndexSet(0, heapsize, heapsize-1))
	ensures hp(a[..], heapsize) 
	ensures multiset(a[..heapsize]) == multiset(oldA[..heapsize-1]+[x])
	modifies a
{
	var current, parentIndex := InitCurrAndP(a,heapsize, x, oldA);
	Heapify(a, heapsize, x, current, parentIndex, oldA);
}

method {:verify false} InitCurrAndP(a: array<int>, heapsize: nat, x: int, ghost oldA: seq<int>) returns(current: nat, parentIndex: int)
	requires 0 < heapsize <= a.Length == |oldA| && a[heapsize-1] == x
	requires multiset(a[..heapsize]) == multiset(oldA[..heapsize-1]+[x])
	requires hp(a[..], heapsize-1) && ph(a[..heapsize], IndexSet(0, heapsize, heapsize-1))
	ensures current == heapsize - 1 && 0 <= current < a.Length && parentIndex == (current - 1) / 2
	{
	current := InitCurr(a, heapsize, x);
	parentIndex := InitParent(a, heapsize, x, current);
}

method {:verify false} InitCurr(a: array<int>, heapsize: nat, x: int) returns(current: nat)
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

method {:verify false} InitParent(a: array<int>, heapsize: nat, x: int, current: nat) returns(parent: int)
	requires 0 < heapsize <= a.Length && a[heapsize-1] == x
	requires multiset(a[..heapsize]) == multiset(a[..heapsize-1]+[x])
	requires hp(a[..], heapsize-1) && 0 <= current < a.Length && current == heapsize - 1
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

method {:verify false} Heapify(a: array<int>, heapsize: nat, x: int, current0: nat, parentIndex0: int,ghost oldA: seq<int>)
	requires current0 == heapsize - 1 && parentIndex0 == (current0 - 1) / 2
	requires 0 <= current0 <= heapsize -1 < a.Length
	requires a.Length == |oldA|
	requires 0 < heapsize <= a.Length && a[heapsize-1] == x
	requires multiset(a[..heapsize]) == multiset(oldA[..heapsize-1]+[x])
	requires hp(a[..], heapsize-1) && ph(a[..heapsize], IndexSet(0, heapsize, current0))
	ensures hp(a[..], heapsize)
	ensures multiset(a[..heapsize]) == multiset(old(a[..]))
	modifies a
{
	var current, parentIndex := current0, parentIndex0; 
	// assert current0 > 0;
	// assert a[current] > a[parentIndex];
	while (Guard1(a[..], current, parentIndex))
		invariant WhileInv(a[..], heapsize, x, current, parentIndex, old(a[..]))
		decreases current
	{ 
		current, parentIndex := LoopBody(a, heapsize, x, current, parentIndex, old(a[..]));
	}
	// WhileInv && !Guard1
}
predicate method Guard1(a: seq<int>, current: nat, parentIndex: int)
	requires 0 <= parentIndex <= current < |a| && parentIndex == (current - 1) / 2
{
	current > 0 && a[current] > a[parentIndex]
}
predicate WhileInv(a: seq<int>, heapsize: nat, x:int, current: nat,parentIndex: int, oldA: seq<int>)
	requires 0 < heapsize <= |a|
	requires 0 <= current < |a|
	requires |a| == |oldA|
{
	multiset(a[..heapsize]) == multiset(oldA[..heapsize]) &&
	ph(a[..], IndexSet(0, heapsize, current))
}


method {:verify false} LoopBody(a: array<int>, heapsize: nat, x: int, current0: nat, parentIndex0: int, ghost oldA: seq<int>) returns (current: nat, parentIndex: int)
	requires  0 <= parentIndex0 <= current0 <= heapsize-1 < a.Length == |oldA| && 0 < heapsize <= a.Length
	requires parentIndex0 == (current0 - 1) / 2 && Guard1(a[..],current0,parentIndex0)
	requires WhileInv(a[..],heapsize,x,current0,parentIndex0,oldA[..])
	ensures WhileInv(a[..], heapsize, x, current, parentIndex, oldA[..])
	modifies a
{
	swap(a, heapsize, x, current0, parentIndex0, oldA); 
	current, parentIndex := setCAndP(a,heapsize,x,current0,parentIndex0,oldA);
}
method {:verify false} swap (a: array<int>, heapsize: nat, x: int, current: nat, parentIndex: int,ghost oldA: seq<int>) 
	requires 0 <= parentIndex <= current <= heapsize-1 < a.Length == |oldA| && 0 < heapsize <= a.Length
	requires parentIndex == (current - 1) / 2 && Guard1(a[..],current,parentIndex)
	requires WhileInv(a[..],heapsize,x,current,parentIndex,oldA)
	ensures current > 0 && multiset(a[..heapsize]) == multiset(old(a[..heapsize]))
	ensures	ph(a[..], IndexSet(0, heapsize, parentIndex))
	modifies a
{
	// Lemma3(a[..],heapsize,x,current,parentIndex,oldA);
	a[current], a[parentIndex] := a[parentIndex], a[current];
}

// lemma {:verify false} Lemma3(a: seq<int>, heapsize: nat, x: int, current: nat, parentIndex: int, oldA: seq<int>)
// 	requires parentIndex == (current - 1) / 2 && current > 0 && |a| == |oldA|
// 	requires 0 < heapsize <= |a[..]| && multiset(a[..heapsize]) == multiset(oldA[..heapsize])
// 	requires 0 <= parentIndex <= current <= heapsize-1 < |a[..]| == |oldA| 
// 	ensures current > 0 && ph(a[..], IndexSet(0, heapsize, parentIndex))
// 	ensures multiset(a[..parentIndex]+[a[current]]+a[parentIndex+1..current]+[a[parentIndex]]+a[current+1..heapsize]) == multiset(oldA[..heapsize])
// {
// 	// var newA := a[..parentIndex]+[a[current]]+a[parentIndex+1..current]+[a[parentIndex]]+a[current+1..heapsize];
// 	// var originA := a[..parentIndex]+[a[parentIndex]]+a[parentIndex+1..current]+[a[current]]+a[current+1..heapsize];
// 	// assert 0 < heapsize <= |originA|;
// 	// assert 0 < heapsize <= |newA|;
// 	// assert 0 <= current < |newA|;
// 	// assert |originA| == heapsize == |newA| == |a[..heapsize]|;
// 	// assert multiset(newA[..parentIndex]+newA[parentIndex+1..current]+newA[current+1..heapsize]) == multiset(a[..parentIndex]+a[parentIndex+1..current]+a[current+1..heapsize]);
//  	// assert multiset(newA[..heapsize]) == multiset(a[..heapsize]);
// 	// assert multiset(a[..parentIndex]+[a[current]]+a[parentIndex+1..current]+[a[parentIndex]]+a[current+1..heapsize]) == multiset(oldA[..heapsize]);
// }

method {:verify false} setCAndP(a: array<int>, heapsize: nat, x: int, current0: nat, parentIndex0: int, ghost oldA: seq<int>) returns(current: nat, parentIndex: int)
	requires  0 <= parentIndex0 <= current0 <= heapsize-1 < a.Length == |oldA| && 0 < heapsize <= a.Length
	requires current0 > 0 && parentIndex0 == (current0 - 1) / 2
	requires multiset(a[..heapsize]) == multiset(oldA[..heapsize])
	ensures current < current0 && parentIndex <= parentIndex0
	ensures WhileInv(a[..], heapsize, x, current, parentIndex, oldA)

{
	Lemma4(a,heapsize,x,current0,parentIndex0,oldA);
	current := parentIndex0; 
	parentIndex := Parent(current);
}

lemma {:verify false} Lemma4(a: array<int>, heapsize: nat, x: int, current: nat, parentIndex: int, oldA: seq<int>)
	requires  0 <= parentIndex <= current <= heapsize-1 < a.Length == |oldA| && 0 < heapsize <= a.Length
	requires current > 0 && parentIndex == (current - 1) / 2
	requires multiset(a[..heapsize]) == multiset(oldA[..heapsize])
	ensures parentIndex < current && ParentFunc(current) <= parentIndex
	ensures WhileInv(a[..], heapsize, x, parentIndex, ParentFunc(current), oldA)
{
	assert 0 < heapsize <= a.Length;
	assert 0 <= current < a.Length;
	assert a.Length == |oldA|;

	assert multiset(a[..heapsize]) == multiset(oldA[..heapsize]);
	assert ph(a[..], IndexSet(0, heapsize, current));
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
