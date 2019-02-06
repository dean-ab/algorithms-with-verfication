predicate Sorted(a: array<int>)
	reads a
{
	forall i,j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
}

predicate SortedSequence(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

method MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
	decreases a.Length

method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b

method Main() {
	var a := new int[3];
	a[0], a[1], a[2] := 4, 8, 6;
	var q0 := a[..];
	assert q0 == [4,8,6];
	a := MergeSort(a);
	assert a.Length == |q0| && multiset(a[..]) == multiset(q0);
	print "the sorted version of [4, 8, 6] is ";
	print a[..];
	assert Sorted(a);
	assert a[..] == [4,6,8];
}
