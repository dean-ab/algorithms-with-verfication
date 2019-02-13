// R. Ettinger, December 2018, following Carroll Morgan's development in "Programming from Specifications", in Dafny v2.2.0
method {:verify false} HeapSort'(a: array<int>)
  ensures Sorted(a) && multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	var j := a.Length / 2;
	while j != 0
	{
		j := j - 1;
		Sift'(a, j, a.Length, multiset(a[..]));
	}
	var i := a.Length;
	while i != 0
	{
		i := i - 1;
		a[0], a[i] := a[i], a[0];
		Sift'(a, 0, i, multiset(a[..]));
	}
}

method {:verify false} Sift'(a: array<int>, l: nat, h: nat, ghost A: multiset<int>)
{
	if l < h
	{
		var k := l;
		while (2*k+2 == h && a[k] < a[2*k+1]) || (2*k+2 < h && (a[k] < a[2*k+1] || a[k] < a[2*k+2]))
		{
			var m;
			if 2*k+2 == h
			{
				m := 2*k+1;
			}
			else if 2*k+2 < h && a[2*k+1] >= a[2*k+2]
			{
				m := 2*k+1;
			}
			else
			{
				m := 2*k+2;
			}
			a[k],a[m] := a[m],a[k];
			k := m;
		}
	}
}

predicate Sorted(a: array<int>)
	reads a
{
	forall i,j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
}

predicate SortedSequence(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
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
predicate fn(q: seq<int>, i: nat)
{
	i <= |q| && SortedSequence(q[i..]) && (forall m,n :: 0 <= m < i <= n < |q| ==> q[m] <= q[n])
}

// for a reason unknown to me, using a predicate such as this in set comprehension expressions
// helps to avoid Dafny's "No terms found to trigger on" warning
predicate InRange(start: nat, i: nat, end: nat) { start <= i < end }
function IndexSet(start: nat, end: nat): set<nat> { set i: nat | i < end && InRange(start, i, end) }

method HeapSort(a: array<int>)
  ensures Sorted(a) && multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	// introduce logical constant + sequential composition + strengthen postcondition
	ghost var A := multiset(a[..]);
	MakeHeap(a, A);
	Sort(a, A);
	assert A == old(multiset(a[..])); // this way the postcondition of Sort is indeed strong enough
}

method MakeHeap(a: array<int>, ghost A: multiset<int>)
	requires multiset(a[..]) == A
	ensures hp(a[..], a.Length) && multiset(a[..]) == A
	modifies a
{
	// introduce local variable + leading assignment + weaken precondition + strengthen poscondition
	var j := a.Length / 2;
	// second half is trivially a partial heap as it contains leaves only
	LemmaMakeHeapPre(a, j, A);
	j := MakeHeapLoop(a, j, A);
	LemmaMakeHeapPost(a, j, A);
}

// proof of weaken precondition step
lemma LemmaMakeHeapPre(a: array<int>, j: nat, A: multiset<int>)
	requires j == a.Length / 2 && multiset(a[..]) == A // precondition of MakeHeap + the initialization
	ensures j <= a.Length / 2 && ph(a[..], IndexSet(j, a.Length)) && multiset(a[..]) == A // precondition of MakeHeapLoop
{}

// proof of the strengthen postcondition
lemma LemmaMakeHeapPost(a: array<int>, j: nat, A: multiset<int>)
	requires 0 == j <= a.Length / 2 && ph(a[..], IndexSet(j, a.Length)) && multiset(a[..]) == A
	ensures	hp(a[..], a.Length) && multiset(a[..]) == A // postcondition of MakeHeap
{
	// indeed, the definition of a heap ("hp") is in terms of a partial heap ("ph") for range 0..a.Length
}

method MakeHeapLoop(a: array<int>, j0: nat, ghost A: multiset<int>) returns (j: nat)
	requires j0 <= a.Length / 2 && ph(a[..], IndexSet(j0, a.Length)) && multiset(a[..]) == A
	ensures 0 == j <= a.Length / 2 && ph(a[..], IndexSet(j, a.Length)) && multiset(a[..]) == A
	modifies a
{
	j := j0;
	// iteration
	while j != 0
		invariant j <= a.Length / 2 && ph(a[..], IndexSet(j, a.Length)) && multiset(a[..]) == A
		decreases j
	{
		j := MakeHeapLoopBody(a, j, A);
	}
}

method MakeHeapLoopBody(a: array<int>, j0: nat, ghost A: multiset<int>) returns (j: nat)
	requires 0 < j0 <= a.Length / 2 && ph(a[..], IndexSet(j0, a.Length)) && multiset(a[..]) == A // pre[j0 \ j0-1]
	ensures j <= a.Length / 2 && ph(a[..], IndexSet(j, a.Length)) && multiset(a[..]) == A // post1[j0 \ j0-1]
	ensures j < j0 // post2[j0 \ j0-1]
	modifies a
{
	j := j0;
	// leading assignment (could combine with further steps but prefer to practice documenting this step alone)
	j := j - 1;
	j := MakeHeapSift(a, j, A);
}

// pre, post1, and post2 here were inferred from the specification of MakeHeapLoopBody above by the inverse substitution:
// the "j0" was replaced by "j0+1" in the precondition and the postcondition
method MakeHeapSift(a: array<int>, j0: nat, ghost A: multiset<int>) returns (j: nat)
	requires 0 < j0 + 1 <= a.Length / 2 && ph(a[..], IndexSet(j0 + 1, a.Length)) && multiset(a[..]) == A // pre
	ensures j <= a.Length / 2 && ph(a[..], IndexSet(j, a.Length)) && multiset(a[..]) == A // post1
	ensures j < j0 + 1 // post2
	modifies a
{
	j := j0;
	// contract frame + weaken precondition + strengthen poscondition
	LemmaMakeHeapSiftPre(a, j, A);
	Sift(a, j, a.Length, A);
	LemmaMakeHeapSiftPost(a, j, A);
}

lemma LemmaMakeHeapSiftPre(a: array<int>, j: nat, A: multiset<int>)
	// precondition of MakeHeapSift
	requires 0 < j + 1 <= a.Length / 2 && ph(a[..], IndexSet(j + 1, a.Length)) && multiset(a[..]) == A
	// precondition of Sift with [l, h \ j, a.Length]
	ensures multiset(a[..]) == A
	ensures j <= a.Length <= a.Length
	ensures ph(a[..], IndexSet(j+1, a.Length)) && fn(a[..], a.Length)
{}

lemma LemmaMakeHeapSiftPost(a: array<int>, j: nat, A: multiset<int>)
	// from the precondition of MakeHeapSift (availabe here since "j" is no longer in the frame)
	requires 0 < j + 1 <= a.Length / 2
	// postcondition of Sift with [l, h \ j, a.Length]
	requires ph(a[..], IndexSet(j, a.Length)) && fn(a[..], a.Length)
	requires multiset(a[..]) == A
	// postcondition of MakeHeapSift with [j \ j0] first (contract frame) and then the "j0" is renamed everywhere back to "j"
	ensures j <= a.Length / 2 && ph(a[..], IndexSet(j, a.Length)) && multiset(a[..]) == A
	ensures j < j + 1
{}

method Sort(a: array<int>, ghost A: multiset<int>)
	requires hp(a[..], a.Length) && multiset(a[..]) == A
	modifies a
	ensures Sorted(a) && multiset(a[..]) == A
{
	// introduce local variable + leading assignment +
	// weaken precondition (proof obligation not included) + iteration
	var i: nat := a.Length;
	while i != 0
		invariant i <= a.Length && hp(a[..], i) && fn(a[..], i) && multiset(a[..]) == A
		decreases i
	{
		i := OuterLoopBody(a, i, A);
	}
}

method OuterLoopBody(a: array<int>, i0: nat, ghost A: multiset<int>) returns (i: nat)
	requires 1 <= i0 <= a.Length && hp(a[..], i0) && fn(a[..], i0) && multiset(a[..]) == A
	ensures i <= a.Length && hp(a[..], i) && fn(a[..], i) && multiset(a[..]) == A
	ensures i < i0
	modifies a
{
	i := i0;
	// leading assignment + contract frame
	i := i - 1;
	ExtractRemainingMax(a, i, A);
}

// again, inferring the spec by an inverse substitution of "i0" replaced by "i0+1"
method ExtractRemainingMax(a: array<int>, i: nat, ghost A: multiset<int>)
	requires 1 <= i+1 <= a.Length && hp(a[..], i+1) && fn(a[..], i+1) && multiset(a[..]) == A
	ensures i <= a.Length && hp(a[..], i) && fn(a[..], i) && multiset(a[..]) == A
	//ensures i < i0+1 (we got this from the leading assignment step; contract frame has turned it into the obviously redundant "i < i+1")
	modifies a
{
	// sequential composition + strengthen poscondition
	ghost var q0 := a[..];
	ExtractRemainingMax1(a, i, A);
	Sift(a, 0, i, A);
	LemmaExtractRemainingMax(a, i, A);
}

// proof obligation of the strengthen poscondition
lemma LemmaExtractRemainingMax(a: array<int>, i: nat, A: multiset<int>)
	requires 1 <= i+1 <= a.Length // a relevant conjunct from pre[w \ w0]
	requires ph(a[..], IndexSet(0, i)) && fn(a[..], i) // post'
	requires multiset(a[..]) == A // post'
	ensures i <= a.Length && hp(a[..], i) && fn(a[..], i) && multiset(a[..]) == A // post
{}

method ExtractRemainingMax1(a: array<int>, i: nat, ghost A: multiset<int>)
	requires 1 <= i+1 <= a.Length && hp(a[..], i+1) && fn(a[..], i+1) && multiset(a[..]) == A
	ensures multiset(a[..]) == A
	//ensures 0 <= a.Length <= a.Length
	ensures ph(a[..], IndexSet(1, i)) && fn(a[..], i)
	modifies a
{
	// assignment
	LemmaExtractRemainingMax1(a, i, A);
	a[0], a[i] := a[i], a[0]; // a[0] is the largest in a[..i+1]; move it into its final position: a[i]
}

// proof of the swap assignment
lemma LemmaExtractRemainingMax1(a: array<int>, i: nat, A: multiset<int>)
	requires 1 <= i+1 <= a.Length && hp(a[..], i+1) && fn(a[..], i+1) && multiset(a[..]) == A
	ensures var q := a[..][0 := a[i]][i := a[0]]; multiset(q) == A && ph(q, IndexSet(1, i)) && fn(q, i)
{
	var q := a[..][0 := a[i]][i := a[0]];
	assert multiset(q) == A by { LemmaSwapMaintainsMultiset(a[..], q, 0, i); }
	assert ph(a[..], IndexSet(1, i));
	assert fn(q, i) by { LemmaRemainingMaxSorted(a[..], q, i); }
}

// the suffix of "a" from index "h" is already sorted, and "a[l,h)" is a partial heap except at index "l";
// re-order elements in "a[l,h)" to make it a partial heap, including at "l".
method Sift(a: array<int>, l: nat, h: nat, ghost A: multiset<int>)
	requires multiset(a[..]) == A
	requires l <= h <= a.Length
	requires ph(a[..], IndexSet(l+1, h)) && fn(a[..], h)
	ensures ph(a[..], IndexSet(l, h)) && fn(a[..], h)
	ensures multiset(a[..]) == A
	modifies a
{
	// alternation + skip command
	if l < h
	{
		Sift1a(a, l, h, A);
	}
	else
	{
		Sift1b(a, l, h, A);
	}
}

method Sift1a(a: array<int>, l: nat, h: nat, ghost A: multiset<int>)
	requires multiset(a[..]) == A
	requires l < h <= a.Length
	requires ph(a[..], IndexSet(l+1, h)) && fn(a[..], h)
	ensures ph(a[..], IndexSet(l, h)) && fn(a[..], h)
	ensures multiset(a[..]) == A
	modifies a
{
	// leading assignment + weaken precondition + strengthen postcondition
	var k := l;
	LemmaSiftLoopPre(a, l, h, k, A);
	k := SiftLoop(a, l, h, k, A);
	LemmaSiftLoopPost(a, l, h, k, A);
}

// proof of the weaken precondition step
lemma LemmaSiftLoopPre(a: array<int>, l: nat, h: nat, k: nat, A: multiset<int>)
	requires multiset(a[..]) == A
	requires k == l < h <= a.Length
	requires ph(a[..], IndexSet(l+1, h)) && fn(a[..], h)
	ensures J(a[..], h, l, k, A)
{}

// proof of the strengthen postcondition step
lemma LemmaSiftLoopPost(a: array<int>, l: nat, h: nat, k: nat, A: multiset<int>)
	requires J(a[..], h, l, k, A) && hi(a[..], l, h, k)
	ensures ph(a[..], IndexSet(l, h)) && fn(a[..], h)
	ensures multiset(a[..]) == A
{}

method SiftLoop(a: array<int>, l: nat, h: nat, k0: nat, ghost A: multiset<int>) returns (k: nat)
	requires J(a[..], h, l, k0, A)
	ensures J(a[..], h, l, k, A) && hi(a[..], l, h, k)
	modifies a
{
	k := k0;
	// iteration, using an equivalent version of the loop guard, one that is both executable and more efficient than the "!hi(...)"
	assert !hi(a[..], l, h, k) == LargerChildInPrefix(a, h, k) by { LemmaEquivalentGuards(a, l, h, k, A); }
	while LargerChildInPrefix(a,h,k)
		invariant J(a[..], h, l, k, A)
		decreases h - k
	{
		assert !hi(a[..], l, h, k) by { LemmaEquivalentGuards(a, l, h, k, A); }
		k := SiftLoopBody(k, h, a, l, A);
		assert !hi(a[..], l, h, k) == LargerChildInPrefix(a, h, k) by { LemmaEquivalentGuards(a, l, h, k, A); }
	}
	assert hi(a[..], l, h, k) by { LemmaEquivalentGuards(a, l, h, k, A); }
}

// proof of the skip command step (when reaching a leaf in the heap)
lemma Sift1b(a: array<int>, l: nat, h: nat, A: multiset<int>)
	requires multiset(a[..]) == A
	requires l == h <= a.Length
	requires ph(a[..], IndexSet(l+1, h)) && fn(a[..], h)
	ensures ph(a[..], IndexSet(l, h)) && fn(a[..], h)
	ensures multiset(a[..]) == A
{}

// the Sift loop guard
predicate method LargerChildInPrefix(a: array<int>, h: nat, k: nat)
	requires k < h <= a.Length
	reads a
{
	(2*k+2 == h && a[k] < a[2*k+1]) || (2*k+2 < h && (a[k] < a[2*k+1] || a[k] < a[2*k+2]))
}

// the Sift loop invariant
predicate J(q: seq<int>, h: nat, l: nat, k: nat, A: multiset<int>)
{
	l <= k < h <= |q| && 
	ph(q, IndexSet(l, h) - {k}) && 
	lo(q, l, h, k) && fn(q, h) && multiset(q) == A
}

method SiftLoopBody(k: nat, h: nat, a: array<int>, l: nat, ghost A: multiset<int>) returns (m: nat)
	requires J(a[..], h, l, k, A)
	requires !hi(a[..], l, h, k)
	ensures J(a[..], h, l, m, A)
	ensures 0 <= h - m < h - k
	modifies a
{
	// following assignment + contract frame
	m := LargestChildIndex(k, h, a, l, A);
	a[k],a[m] := a[m],a[k];
}

method LargestChildIndex(k: nat, h: nat, a: array<int>, l: nat, ghost A: multiset<int>) returns (m: nat)
	requires J(a[..], h, l, k, A)
	requires !hi(a[..], l, h, k)
	// the first conjunct in the following postcondition is part of the second conjunct (J) too;
	// it is needed here earlier, though, for validity of the sequence assignment
	ensures m < h && J(a[..][k := a[m]][m := a[k]], h, l, m, A)
	ensures 0 <= h - m < h - k
{
	assert 2*k+2 == h || 2*k+2 < h by { LemmaLargerChildInRange(a, l, h, k); }
	// alternation (with three alternatives)
	if 2*k+2 == h
	{
		m := SingleChildIndex(k, h, a, l, A);
	}
	else if 2*k+2 < h && a[2*k+1] >= a[2*k+2]
	{
		m := LeftChildLarger(k, h, a, l, A);
	}
	else
	{
		m := RightChildLarger(k, h, a, l, A);
	}
}

method SingleChildIndex(k: nat, h: nat, a: array<int>, l: nat, ghost A: multiset<int>) returns (m: nat)
	requires 2*k+2 == h // guard
	requires J(a[..], h, l, k, A)
	requires !hi(a[..], l, h, k)
	ensures m < h && J(a[..][k := a[m]][m := a[k]], h, l, m, A)
	ensures 0 <= h - m < h - k
{
	// assignment
	LemmaSingleChild(a, l, h, k, A);
	m := 2*k+1;
}

method LeftChildLarger(k: nat, h: nat, a: array<int>, l: nat, ghost A: multiset<int>) returns (m: nat)
	requires J(a[..], h, l, k, A)
	requires !hi(a[..], l, h, k)
	requires 2*k+2 < h && a[2*k+1] >= a[2*k+2] // guard
	ensures m < h && J(a[..][k := a[m]][m := a[k]], h, l, m, A)
	ensures 0 <= h - m < h - k
{
	// assignment
	LemmaLeftChildLarger(a, l, h, k, A);
	m := 2*k+1;
}

method RightChildLarger(k: nat, h: nat, a: array<int>, l: nat, ghost A: multiset<int>) returns (m: nat)
	requires J(a[..], h, l, k, A)
	requires !hi(a[..], l, h, k)
	requires 2*k+2 < h && a[2*k+1] < a[2*k+2] // guard
	ensures m < h && J(a[..][k := a[m]][m := a[k]], h, l, m, A)
	ensures 0 <= h - m < h - k
{
	// assignment
	LemmaRightChildLarger(a, l, h, k, A);
	m := 2*k+2;
}

// proof of assignment step
lemma LemmaSingleChild(a: array<int>, l: nat, h: nat, k: nat, A: multiset<int>)
	requires 2*k+2 == h // guard
	requires J(a[..], h, l, k, A)
	requires !hi(a[..], l, h, k)
	ensures 2*k+1 < h && J(a[..][k := a[2*k+1]][2*k+1 := a[k]], h, l, 2*k+1, A)
	ensures 0 <= h - (2*k+1) < h - k
{
	var q := a[..];
	assert ph(q[k := q[2*k+1]], IndexSet(l, h) - {2*k+1}) by { LemmaSingleChild2(q, l, h, k); }
}

lemma LemmaSingleChild2(q: seq<int>, l: nat, h: nat, k: nat)
	requires 2*k+2 == h // guard
	requires l <= k < h <= |q| && ph(q, IndexSet(l, h) - {k}) // loop inv.
	ensures ph(q[k := q[2*k+1]], IndexSet(l, h) - {2*k+1})
	// we had all but k in the heap;
	// we update q[k] and must ensure it is also in the heap;
	// none of its children is in range (2*k+2 == h, and 2*k+1 is the newly excluded element);
	// what about its ancestors? if there is any, it was an ancestor of 2*k+1 (which is the new element at k) so was larger!
{
	var s1,s2 := IndexSet(l, h)- {k},IndexSet(l, h) - {2*k+1};
	var q' := q[k := q[2*k+1]];
	forall i,j | i in s2 && j in s2 && AncestorIndex(i,j) ensures q'[i] >= q'[j] {
		if i == j
		{ // trivial
		}
		else if j == k
		{
			assert q'[i] == q[i] >= q[2*k+1] == q'[j] by
			{ 
				assert AncestorIndex(i,2*k+1) by { assert AncestorIndex(i,k) && AncestorIndex(k,2*k+1); LemmaTransitiveAncestors(i,k,2*k+1); }
				assert i in s1 && 2*k+1 in s1 && AncestorIndex(i,2*k+1) && ph(q, s1);
			}
		}
		else
		{
			assert i != k by { assert 2*k+2 == h && 2*k+1 !in s2; } // k's children are out of range yet i is an ancestor of j (!= i)
			assert q'[i] == q[i] >= q[j] == q'[j] by { assert i in s1 && j in s1 && AncestorIndex(i,j) && ph(q, s1); }
		}
	}
}

// proof of assignment step
lemma LemmaLeftChildLarger(a: array<int>, l: nat, h: nat, k: nat, A: multiset<int>)
	requires J(a[..], h, l, k, A)
	requires !hi(a[..], l, h, k)
	requires 2*k+2 < h && a[2*k+1] >= a[2*k+2] // guard
	ensures 2*k+1 < h && J(a[..][k := a[2*k+1]][2*k+1 := a[k]], h, l, 2*k+1, A)
	ensures 0 <= h - (2*k+1) < h - k
{
	var q := a[..];
	assert ph(q[k := q[2*k+1]], IndexSet(l, h) - {2*k+1}) by { LemmaLeftChildLarger2(q, l, h, k); }
}

lemma LemmaLeftChildLarger2(q: seq<int>, l: nat, h: nat, k: nat)
	requires l <= k < h <= |q| && ph(q, IndexSet(l, h) - {k}) // loop inv.
	requires 2*k+2 < h && q[2*k+1] >= q[2*k+2] // guard
	ensures ph(q[k := q[2*k+1]], IndexSet(l, h) - {2*k+1})
{
	LemmaLargerChild(q,l,h,k,2*k+2,2*k+1);
}

lemma LemmaLargerChild(q: seq<int>, l: nat, h: nat, k: nat, lc: nat, hc: nat)
	requires l <= k < h <= |q| && ph(q, IndexSet(l, h) - {k}) // loop inv.
	requires (lc == 2*k+1 && hc == 2*k+2) || (lc == 2*k+2 && hc == 2*k+1) // children of k: lower and higher
	requires 2*k+2 < h && q[hc] >= q[lc] // guard
	ensures ph(q[k := q[hc]], IndexSet(l, h) - {hc})
	// we had all but k in the heap;
	// we update q[k] and must ensure it is also in the heap;
	// one of its children is in range (lc) whereas the other (hc) is the newly excluded element;
	// and the guard ensures the new element at k (previously at q[hc]) is >= q[lc]);
	// what about its ancestors? if there is any, it was an ancestor of hc (which is the new element at k) so was larger!
{
	var s1,s2 := IndexSet(l, h) - {k},IndexSet(l, h) - {hc};
	var q' := q[k := q[hc]];
	forall i,j | i in s2 && j in s2 && AncestorIndex(i,j) ensures q'[i] >= q'[j] {
		if i == j
		{ // trivial
		}
		else if j == k
		{
			assert q'[i] == q[i] >= q[hc] == q'[j] by
			{ 
				assert AncestorIndex(i,hc) by { assert AncestorIndex(i,k) && AncestorIndex(k,hc); LemmaTransitiveAncestors(i,k,hc); }
				assert i in s1 && hc in s1 && AncestorIndex(i,hc) && ph(q, s1);
			}
		}
		else if i == k && AncestorIndex(hc,j)
		{
			assert q'[i] == q[hc] >= q[lc];
			assert q'[i] == q[hc] >= q[j] == q'[j] by { assert hc in s1 && j in s1 && AncestorIndex(hc,j) && ph(q, s1); }
		}
		else if i == k
		{
			assert AncestorIndex(lc,j) by { assert AncestorIndex(i,j) && !AncestorIndex(hc,j) && i == k != j; }
			assert q'[i] == q[hc] >= q[lc] >= q[j] == q'[j] by { assert lc in s1 && j in s1 && AncestorIndex(lc,j) && ph(q, s1); }
		}
		else
		{
			//assert i != k by { assert lc == h && hc !in s2; } // k's children are out of range yet i is an ancestor of j (!= i)
			assert q'[i] == q[i] >= q[j] == q'[j] by { assert i in s1 && j in s1 && AncestorIndex(i,j) && ph(q, s1); }
		}
	}
}

// proof of assignment step
lemma LemmaRightChildLarger(a: array<int>, l: nat, h: nat, k: nat, A: multiset<int>)
	requires J(a[..], h, l, k, A)
	requires !hi(a[..], l, h, k)
	requires 2*k+2 < h && a[2*k+1] < a[2*k+2] // guard
	ensures 2*k+2 < h && J(a[..][k := a[2*k+2]][2*k+2 := a[k]], h, l, 2*k+2, A)
	ensures 0 <= h - (2*k+2) < h - k
{
	var q := a[..];
	assert ph(q[k := q[2*k+2]], IndexSet(l, h) - {2*k+2}) by { LemmaRightChildLarger2(q, l, h, k); }
}

// same as LemmaLeftChildLarger2 above, with 2*k+1 for 2*k+2 and vice versa.
lemma LemmaRightChildLarger2(q: seq<int>, l: nat, h: nat, k: nat)
	requires l <= k < h <= |q| && ph(q, IndexSet(l, h) - {k}) // loop inv.
	requires 2*k+2 < h && q[2*k+1] < q[2*k+2] // guard
	ensures ph(q[k := q[2*k+2]], IndexSet(l, h) - {2*k+2})
{
	LemmaLargerChild(q,l,h,k,2*k+1,2*k+2);
}

// there is a larger descendent in range, so there must be at least one child in range
lemma LemmaLargerChildInRange(a: array<int>, l: nat, h: nat, k: nat) // possible cases: 2*k+2 == h || 2*k+2 < h
	requires l <= h <= a.Length && k < a.Length
	requires !hi(a[..], l, h, k)
	ensures 2*k+2 <= h
{
	calc {
		!hi(a[..], l, h, k);
	==
		!(forall j :: l <= j < h && AncestorIndex(k, j) ==> a[k] >= a[j]);
	==
		exists j :: l <= j < h && AncestorIndex(k, j) && a[k] < a[j];
	==>
		exists j :: l <= j < h && AncestorIndex(k, j) && k != j;
	==> { assert forall i:nat,j:nat :: AncestorIndex(i, j) && i != j ==> j >= 2*i+1; }
		exists j :: l <= j < h && AncestorIndex(k, j) && k != j && j >= 2*k+1;
	==>
		2*k+1 < h;
	==>
		2*k+2 <= h;
	}
}

predicate Swapped(q0: seq<int>, q1: seq<int>, i: nat, j: nat)
	requires 0 <= i < |q0| == |q1|
	requires 0 <= j < |q1|
{
	q0[i] == q1[j] && q0[j] == q1[i] && 
	(forall k :: 0 <= k < |q0| && k != i && k != j ==> q0[k] == q1[k])
}

lemma LemmaRemainingMaxSorted(q0: seq<int>, q1: seq<int>, i : nat)
	requires i < |q0| == |q1| && hp(q0, i+1) && fn(q1, i+1)
	requires Swapped(q0, q1, 0, i)
	ensures fn(q1, i)
	// a[i] is q[0], the root of the heap a[..i+1], due to Swapped(q0, a[..], 0, i);
	// hence a[i] is >= all elements in a[..i] (which is [q[i]]+q[1..i]), again due to Swapped
	// and a[i] is <= all elements in a[i+1..] (due to fn(a[..], i+1));
	// and so we get fn(a[..], i) as needed
{
	assert 	i <= |q1| && SortedSequence(q1[i..]);
	assert forall m,n :: 0 <= m < i <= n < |q1| ==> q1[m] <= q1[n] by
	{
		assert forall m,n :: 0 <= m < i+1 <= n < |q1| ==> q1[m] <= q1[n] by { assert fn(q1, i+1); }
		assert forall m :: 0 <= m < i ==> q1[m] <= q1[i] by
		{
			assert q1[i] == q0[0] by { assert Swapped(q0,q1,0,i); }
			assert forall m: nat :: m <= i && AncestorIndex(0,m) ==> q0[0] >= q0[m] by { assert hp(q0, i+1); }
			assert forall m: nat :: m <= i ==> q0[0] >= q0[m] by
			{
				assert hp(q0, i+1);
				forall m: nat ensures AncestorIndex(0,m) { LemmaRootIsAncestor(m); }
			}
			assert forall m :: 0 < m < i ==> q1[m] == q0[m] <= q0[0] == q1[i] by { assert hp(q0, i+1); }
		}
	}
}

lemma LemmaRootIsAncestor(j: nat) ensures AncestorIndex(0,j)
{
	if j == 0
	{
		assert AncestorIndex(0,0);
	}
	else
	{
		var i := if j%2 == 1 then j/2 else j/2-1;
		assert AncestorIndex(i,j) by { assert if j%2 == 1 then j == 2*i+1 else j == 2*i+2; }
		assert AncestorIndex(0,i) by { LemmaRootIsAncestor(i); }
		assert AncestorIndex(0,j) by { LemmaTransitiveAncestors(0,i,j); }
	}
} 

lemma LemmaTransitiveAncestors(i: nat, j: nat, k: nat)
	requires AncestorIndex(i,j)
	requires AncestorIndex(j,k)
	ensures AncestorIndex(i,k)
	decreases j-i
{
	if i == j || j == k
	{ // trivial
	}
	else
	{
		assert i < j < k;
		if AncestorIndex(2*i+1, j)
		{
			LemmaTransitiveAncestors(2*i+1, j, k);
		}
		else
		{
			assert AncestorIndex(2*i+2, j);
			LemmaTransitiveAncestors(2*i+2, j, k);
		}
	}
}

lemma LemmaSwapMaintainsMultiset(q0: seq<int>, q1: seq<int>, i: nat, j: nat)
	requires 0 <= i < |q0| == |q1|
	requires 0 <= j < |q1|
	requires Swapped(q0, q1, i, j)
	ensures multiset(q0) == multiset(q1)
{
	if (i == j) {
		assert multiset(q0) == multiset(q1) by { assert q0 == q1; }
	} else if (i < j) {
		calc {
			multiset(q0);
		== { assert q0 == q0[..i]+[q0[i]]+q0[i+1..j]+[q0[j]]+q0[j+1..]; }
			multiset(q0[..i]+[q0[i]]+q0[i+1..j]+[q0[j]]+q0[j+1..]);
		==
			multiset(q0[..i])+multiset([q0[i]])+multiset(q0[i+1..j])+multiset([q0[j]])+multiset(q0[j+1..]);
		== { assert q0[..i] == q1[..i] && q0[i+1..j] == q1[i+1..j] && q0[j+1..] == q1[j+1..] by { assert Swapped(q0,q1,i,j); } }
			multiset(q1[..i])+multiset([q0[i]])+multiset(q1[i+1..j])+multiset([q0[j]])+multiset(q1[j+1..]);
		== { assert q0[i] == q1[j] && q0[j] == q1[i] by { assert Swapped(q0,q1,i,j); } }
			multiset(q1[..i])+multiset([q1[j]])+multiset(q1[i+1..j])+multiset([q1[i]])+multiset(q1[j+1..]);
		==
			multiset(q1[..i])+multiset([q1[i]])+multiset(q1[i+1..j])+multiset([q1[j]])+multiset(q1[j+1..]);
		==
			multiset(q1[..i]+[q1[i]]+q1[i+1..j]+[q1[j]]+q1[j+1..]);
		== { assert q1 == q1[..i]+[q1[i]]+q1[i+1..j]+[q1[j]]+q1[j+1..]; }
			multiset(q1);
		}
	} else {
		assert i > j;
		LemmaSwapMaintainsMultiset(q0,q1,j,i);
	}
}

lemma LemmaEquivalentGuards(a: array<int>, l: nat, h: nat, k: nat, A: multiset<int>)
	requires J(a[..], h, l, k, A)
	ensures LargerChildInPrefix(a,h,k) == !hi(a[..], l, h, k)
	// whenever the loop invariant J(a[..], h, l, k, A) holds,
	// a child of k in the first h elements of a is larger that the value at k iff !hi(a[..], l, h, k);
	// ...this equivalence justifies the implementation Sift's loop guard through the executable
	// predicate method LargerChildInPrefix(a,h,k)
{
	// recalling the definition of J:
	assert l <= k < h <= a.Length;
	assert ph(a[..], IndexSet(l, h) - {k});
	assert lo(a[..], l, h, k);
	assert fn(a[..], h);
	assert multiset(a[..]) == A;
	// only the first three above seem relevant here
	calc {
		!hi(a[..], l, h, k);
	==
		!(forall j :: l <= j < h && AncestorIndex(k, j) ==> a[k] >= a[j]);
	==
		exists j :: l <= j < h && AncestorIndex(k, j) && a[k] < a[j];
	}
	if 2*k+2 == h
	{ // k has only one child in range
		calc {
			exists j :: l <= j < h && AncestorIndex(k, j) && a[k] < a[j];
		==
			a[k] < a[2*k+1];
		== { assert 2*k+2 == h; }
			(2*k+2 == h && a[k] < a[2*k+1]) || (2*k+2 < h && (a[k] < a[2*k+1] || a[k] < a[2*k+2]));
		==
			LargerChildInPrefix(a,h,k);
		}
	}
	else
	{ // k has only one child in range
		assert !hi(a[..], l, h, k) ==> 2*k+2 < h; // k has two children in range
		calc {
			exists j :: l <= j < h && AncestorIndex(k, j) && a[k] < a[j];
		==
			2*k+2 < h && (a[k] < a[2*k+1] || a[k] < a[2*k+2]);
		== { assert 2*k+2 != h; }
			(2*k+2 == h && a[k] < a[2*k+1]) || (2*k+2 < h && (a[k] < a[2*k+1] || a[k] < a[2*k+2]));
		==
			LargerChildInPrefix(a,h,k);
		}
	}
}

// method Main() {
// 	var a: array<int> := new int[3];
// 	a[0], a[1], a[2] := 4, 8, 6;
// 	var q0: seq<int> := a[..];
// 	assert q0 == [4,8,6];
// 	HeapSort(a);
// 	assert multiset(a[..]) == multiset(q0);
// 	print "the sorted version of [4, 8, 6] is ";
// 	print a[..];
// 	assert Sorted(a);
// 	assert a[..] == [4,6,8];

// 	a := new int[5];
// 	a[0], a[1], a[2], a[3], a[4] := 3, 8, 5, -1, 10;
// 	q0 := a[..];
// 	assert q0 == [3, 8, 5, -1, 10];
// 	HeapSort(a);
// 	assert multiset(a[..]) == multiset(q0);
// 	print "\nthe sorted version of [3, 8, 5, -1, 10] is ";
// 	print a[..];
// 	assert Sorted(a);
// 	//assert a[..] == [-1, 3, 5, 8, 10];

// 	assert AncestorIndex(0,0);
// 	assert AncestorIndex(0,1);
// 	assert AncestorIndex(0,2);
// 	assert AncestorIndex(0,3); // <0,1,3>
// 	assert AncestorIndex(0,4); // <0,1,4>
// 	assert !AncestorIndex(1,0);
// 	assert AncestorIndex(1,1);
// 	assert !AncestorIndex(1,2);
// 	assert AncestorIndex(1,3);
// 	assert AncestorIndex(1,4);
// 	assert !AncestorIndex(2,0);
// 	assert !AncestorIndex(2,1);
// 	assert AncestorIndex(2,2);
// 	assert !AncestorIndex(2,3);
// 	assert !AncestorIndex(2,4);
// 	assert AncestorIndex(2,5);
// 	assert AncestorIndex(2,6);
// }