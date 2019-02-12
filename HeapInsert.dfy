// include "CCPR191-HeapSort-complete-30Dec18.dfy"

method {:verify true} Parent(index: nat) returns (p: int) 
	ensures p == (index - 1) / 2
	ensures p <= index
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
	(forall i,j :: i in s && j in s && AncestorIndex(i, j) ==> q[i] >= q[j])
}

predicate phAndHi(q: seq<int>, s: set<nat>, k: nat)
	requires (forall e :: e in s ==> e < |q|)
{
	(forall i,j :: i in s && j in s && AncestorIndex(i, j) ==> q[i] >= q[j]) &&
	forall j :: j in s && AncestorIndex(k, j) ==> q[k] >= q[j]
}
// element k is a valid heap element (in the given range) with respect to its ancestors (lower indices)
predicate lo(q: seq<int>, s: set<nat>, k: nat)
    requires k < |q| && (forall e :: e in s ==> e < |q|)
{
	forall i :: i in s && AncestorIndex(i, k) ==> q[i] >= q[k]
}
// element k is a valid heap element (in the given range) with respect to its descendents (higher indices)
predicate hi(q: seq<int>, s: set<nat>, k: nat)
	requires k < |q| && (forall e :: e in s ==> e < |q|)
{
	forall j :: j in s && AncestorIndex(k, j) ==> q[k] >= q[j]
}
// the suffix q[i..] holds elements in their final (sorted) positions

function IndexSet(start: nat, end: nat, except: nat): set<nat> {
	 set i: nat | start <= i < end && i != except }

method HeapInsert(a: array<int>, heapsize: nat, x: int)
	requires heapsize < a.Length
	requires hp(a[..], heapsize)
	ensures hp(a[..], heapsize+1)
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
	modifies a
{
    // Sequantial Composition
    HeapInsert1a(a, heapsize, x);	
	HeapInsert1b(a, heapsize + 1, x, multiset(old(a[..heapsize])+ [x]));	
}

method HeapInsert1a(a: array<int>, heapsize: nat, x: int)
    requires heapsize < a.Length
	requires hp(a[..], heapsize)
    ensures 0 < heapsize + 1 <= a.Length
    ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
    ensures phAndHi(a[..heapsize+1], IndexSet(0, heapsize+1, heapsize), heapsize)
    modifies a
{
    // Assignment
    Lemma1(a, heapsize, x);
    a[heapsize] := x;
}

lemma Lemma1 (a: array<int>, heapsize: nat, x: int)
    requires heapsize < a.Length
	requires hp(a[..], heapsize)
    ensures var newA := a[..heapsize]+[x]; 0 < heapsize + 1 <= |newA| && 
    multiset(newA) == multiset(a[..heapsize]+[x]) && 
    phAndHi(newA[..heapsize+1], IndexSet(0, heapsize+1, heapsize), heapsize)
{}

method {:verify true} HeapInsert1b(a: array<int>, heapsize: nat, x: int, ghost oldA: multiset<int>)
    requires 0 < heapsize <= a.Length
    requires multiset(a[..heapsize]) == oldA
    requires phAndHi(a[..heapsize], IndexSet(0, heapsize, heapsize-1), heapsize-1)
    ensures hp(a[..], heapsize)
	ensures multiset(a[..heapsize]) == oldA
	modifies a
{
	var current, parentIndex := InitCurrAndP(a,heapsize, x);
	Heapify(a, heapsize, x, current, parentIndex, oldA);
}

method {:verify true} InitCurrAndP(a: array<int>, heapsize: nat, x: int) returns(current: nat, parentIndex: int)
    requires 0 < heapsize <= a.Length
    requires phAndHi(a[..heapsize], IndexSet(0, heapsize, heapsize-1), heapsize-1)
    ensures current == heapsize - 1 && 0 <= current < a.Length && 
    parentIndex == (current - 1) / 2

	{
	current := InitCurr(a, heapsize, x);
	parentIndex := InitParent(a, heapsize, x, current);
}

method {:verify true} InitCurr(a: array<int>, heapsize: nat, x: int) returns(current: nat)
    requires 0 < heapsize <= a.Length
    requires phAndHi(a[..heapsize], IndexSet(0, heapsize, heapsize-1), heapsize-1)
    ensures current == heapsize - 1 && 0 <= current < a.Length
	{
	LemmaCurr(a, heapsize, x);
	current := heapsize - 1; 
}
lemma LemmaCurr (a: array<int>, heapsize: nat, x: int)
	requires 0 < heapsize <= a.Length
    requires phAndHi(a[..heapsize], IndexSet(0, heapsize, heapsize-1), heapsize-1)
	ensures 0 <= heapsize - 1 < a.Length && heapsize - 1 == heapsize - 1
{}
method {:verify true} InitParent(a: array<int>, heapsize: nat, x: int, current: nat) returns(parent: int)
    requires 0 < heapsize <= a.Length
    requires phAndHi(a[..heapsize], IndexSet(0, heapsize, heapsize-1), heapsize-1)
    requires current == heapsize - 1 && 0 <= current < a.Length 
	ensures parent == (current - 1) / 2
{
	LemmaParent(a, heapsize, x, current);
	parent := Parent(current);
}
lemma LemmaParent (a: array<int>, heapsize: nat, x: int, current: nat)
    requires 0 < heapsize <= a.Length
    requires phAndHi(a[..heapsize], IndexSet(0, heapsize, heapsize-1), heapsize-1)
    requires current == heapsize - 1 && 0 <= current < a.Length 
	ensures ParentFunc(current) == (current - 1) / 2    
{}

method {:verify true} Heapify(a: array<int>, heapsize: nat, x: int, current0: nat, parentIndex0: int,ghost oldA: multiset<int>)
    requires 0 < heapsize <= a.Length
    requires multiset(a[..heapsize]) == oldA
    requires phAndHi(a[..heapsize], IndexSet(0, heapsize, heapsize-1), current0)
    requires current0 == heapsize - 1 && 0 <= current0 < a.Length && 
    parentIndex0 == (current0 - 1) / 2
    ensures hp(a[..], heapsize)
	ensures multiset(a[..heapsize]) == oldA
	modifies a
{
	var current, parentIndex := current0, parentIndex0; 
	while (Guard1(a, current, parentIndex,heapsize))
		invariant WhileInv(a, heapsize, x, current, parentIndex, multiset(old(a[..heapsize])))
		decreases current
	{ 
		current, parentIndex := LoopBody(a, heapsize, x, current, parentIndex, multiset(old(a[..heapsize])));
	}
	// WhileInv && !Guard1
}

predicate method Guard1(a: array<int>, current: nat, parentIndex: int, heapsize: nat)
    reads a
{
	0 < current < heapsize <= a.Length && 
    0 <= parentIndex < heapsize <= a.Length &&
    a[current] > a[parentIndex]
}

predicate WhileInv(a: array<int>, heapsize: nat, x:int, current: nat,parentIndex: int, oldA: multiset<int>)
    reads a
{
    parentIndex == (current - 1) / 2 &&
	0 < heapsize <= a.Length && multiset(a[..heapsize]) == oldA &&
	phAndHi(a[..heapsize], IndexSet(0, heapsize, current),current)
}

method {:verify true} LoopBody(a: array<int>, heapsize: nat, x: int, current0: nat, parentIndex0: int, ghost oldA: multiset<int>) returns (current: nat, parentIndex: int)
    requires 0 < heapsize <= a.Length
    requires multiset(a[..heapsize]) == oldA
    requires Guard1(a, current0, parentIndex0,heapsize) && WhileInv(a, heapsize, x, current0, parentIndex0, oldA)
    ensures WhileInv(a, heapsize, x, current, parentIndex, oldA)
	modifies a
{
	swap(a, heapsize, x, current0, parentIndex0, oldA); 
	// current, parentIndex := setCAndP(a,heapsize,x,current0,parentIndex0,oldA);
}

method {:verify true} swap (a: array<int>, heapsize: nat, x: int, current: nat, parentIndex: int,ghost oldA: multiset<int>) 
    requires Guard1(a, current, parentIndex,heapsize)
    requires WhileInv(a, heapsize, x, current, parentIndex, oldA)
    ensures var newA := a[..][current := a[parentIndex]][parentIndex := a[current]];
    // ensures var newA := a[..parentIndex]+[a[current]]+a[parentIndex+1..current]+[a[parentIndex]]+a[current+1..heapsize];
    && multiset(newA[..heapsize]) == oldA &&
    0 < heapsize <= a.Length &&
    phAndHi(newA[..heapsize], IndexSet(0, heapsize, parentIndex),parentIndex)
	modifies a
{
	Lemma2(a ,heapsize,x,current,parentIndex,oldA);
	a[current], a[parentIndex] := a[parentIndex], a[current];
}

lemma Lemma2(a: array<int>, heapsize: nat, x: int, current: nat, parentIndex: int, oldA: multiset<int>) 
    requires Guard1(a, current, parentIndex,heapsize)
    requires WhileInv(a, heapsize, x, current, parentIndex, oldA)
    ensures var newA := a[..][current := a[parentIndex]][parentIndex := a[current]];
    && multiset(newA[..heapsize]) == oldA &&
    0 < heapsize <= a.Length &&
    phAndHi(newA[..heapsize], IndexSet(0, heapsize, parentIndex),parentIndex)
{
    var newA := a[..][current := a[parentIndex]][parentIndex := a[current]];
    var sParent := IndexSet(0, heapsize, parentIndex);
    var sCurr := IndexSet(0, heapsize, current);
    var q,k:= newA[..heapsize], parentIndex;
    var bliPAndC := IndexSet(0, heapsize, parentIndex) - {current};

    assert ph(a[..heapsize], IndexSet(0, heapsize, current));
    assert hi(a[..heapsize],IndexSet(0, heapsize, current),parentIndex);
    assert IndexSet(0, heapsize, current) == IndexSet(0, parentIndex, current) - IndexSet(0, parentIndex, parentIndex)
    assert lo(a[..heapsize],IndexSet(0, heapsize, current),parentIndex) ==>
    lo(newA[..heapsize],IndexSet(0, parentIndex, current),current);
    
    assert hi(newA[..heapsize],IndexSet(0, heapsize, parentIndex),current);

    // (forall j :: j in sParent && AncestorIndex(current, j) ==> newA[current] >= newA[j]) &&
    // (forall j :: j in sParent && AncestorIndex(j, current) ==> newA[j] >= newA[current]);


    // assert forall j :: j in s && AncestorIndex(k, j) ==> q[k] >= q[j];
    // assert forall i,j :: i in bliPAndC && j in bliPAndC && AncestorIndex(i, j) ==> q[i] >= q[j];
    // assert forall i,j :: i in s && j in s && AncestorIndex(i, j) ==> q[i] >= q[j];
}
