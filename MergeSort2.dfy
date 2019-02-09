predicate Sorted(a: array<int>)
	reads a
{
	forall i,j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
}

predicate SortedSequence(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

predicate isValidIndex (a: array<int>, i: nat) 
{
    0 <= i < a.Length
}

method MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
	decreases a.Length
{
    // Alternation
    if (a.Length < 2) {
			b := Assign1(a);
		} else {
			b := MergeSort1(a);
		}
}

method Assign1 (a: array<int>) returns (b: array<int>)
	requires a.Length < 2 // If test
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
{
    // Assignment
	LemmaS1(a);
	b := a;
}

lemma LemmaS1 (a: array<int>) 
	requires a.Length < 2
	ensures a.Length == a.Length && Sorted(a) && multiset(a[..]) == multiset(a[..])
{}

method MergeSort1 (a: array<int>) returns (b: array<int>)
	requires a.Length >= 2 // !(If test)
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
	decreases a.Length
{
	// Sequential Composition
	var middle := AssignMiddle(a);
	b := MergeSort2(a, middle);

}

method AssignMiddle (a: array<int>) returns (m: nat) 
	requires a.Length >= 2
	ensures m == (a.Length - 1) / 2 && isValidIndex(a, m)
{
    // Assignment
	LemmaS2(a);
	m := (a.Length - 1) / 2;
}

lemma LemmaS2 (a: array<int>) 
	requires a.Length >= 2
	ensures (a.Length - 1) / 2 == (a.Length - 1) / 2 && isValidIndex(a, (a.Length - 1) / 2)
{}

method MergeSort2 (a: array<int>, middle: nat) returns (b: array<int>) 
	requires a.Length >= 2
	requires middle == (a.Length - 1) / 2 && isValidIndex(a, middle)
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
	decreases a.Length
{
	// Sequential Composition
	var left, right, i1, i2 := Assign3Split(a, middle);
	b := MergeSort3(a, left, right, middle, i1, i2);
}

method Assign3Split (a: array<int>, middle: nat) returns (left: array<int>, right: array<int>, i1: nat, i2: nat)
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && isValidIndex(a, middle)
	ensures isLeftArr(a, left, middle, i1)
	ensures isRightArr(a, right, middle, i2)
	ensures left.Length + right.Length == a.Length
{
    // Sequential Composition
	left, i1 := Assign3Left(a, middle);
	assert isLeftArr(a, left, middle, i1) ==> forall j :: 0 <= j < left.Length ==> left[j] == a[j];
	right, i2 :=  Assign3Right(a, middle);
	assert isRightArr(a, right, middle, i2) ==> forall j :: 0 <= j < right.Length ==> right[j] == a[j + middle + 1];

}

method Assign3Left(a: array<int>, middle: nat) returns (arr: array<int>, i: nat) 
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && isValidIndex(a, middle) 
	ensures isLeftArr(a, arr, middle, i) && arr.Length == middle + 1
{
	i := 0;
	arr := new int[middle+1];
	while (i != arr.Length) 
		decreases arr.Length - i
		invariant Inv1(a, arr, i)
	{
		ghost var V0 := middle + 1 - i;
		// Following Assignment
		LeftLoopBody(arr, a, i, middle); 
		assert 0 <= arr.Length - i - 1 < V0;
		i := i+1;
		assert 0 <= arr.Length - i < V0;
	}
} 

predicate Inv1(a: array<int>, arr: array<int>, i: nat)
	reads a, arr
{
	i <= arr.Length && isValidIndex(a, i) &&
	forall j :: 0 <= j < i  ==> arr[j] == a[j]
}

predicate isLeftArr(a: array<int>, left: array<int>, middle: nat, i: nat)
	reads left, a
{
	 i == left.Length && Inv1(a, left, i) 
}

predicate isRightArr(a: array<int>, right: array<int>, middle: nat, i: nat)
	reads right, a
{
	i == right.Length && Inv2(a, right, middle, i)
}

method LeftLoopBody(arr: array<int>, a: array<int>, i: nat, middle: nat) 
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && isValidIndex(a, middle) 
	requires i < arr.Length == middle + 1
	requires Inv1(a, arr, i)
	ensures Inv1(a, arr, i+1)
	modifies arr
{
	LemmaArrI(arr, a, i, middle);
	arr[i] := a[i];
} 

lemma LemmaArrI(arr: array<int>, a: array<int>, i: nat, middle: nat)
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && i < arr.Length == middle + 1 && isValidIndex(a, middle) 
	requires Inv1(a, arr, i)
	ensures a[..i] + [a[i]] == a[..i+1]
{}

method Assign3Right(a: array<int>, middle: nat) returns (arr: array<int>, i: nat) 
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && isValidIndex(a, middle) 
	ensures isRightArr(a, arr, middle, i) && arr.Length == a.Length - (middle + 1)
{
	i := 0;
	arr := new int[a.Length - (middle + 1)];
	while (i != arr.Length)
		decreases arr.Length - i
		invariant Inv2(a, arr, middle, i)
	{
		ghost var V0 := middle + 1 - i;
		// Following Assignment
		RightLoopBody(arr, a, i, middle); 
		assert 0 <= arr.Length - i - 1 < V0;
		i := i+1;
		assert 0 <= arr.Length - i < V0;
	}
} 

predicate Inv2(a: array<int>, arr: array<int>, middle: nat, i: nat)
	reads a, arr
{
	i <= arr.Length == a.Length - (middle + 1) && isValidIndex(a, i) &&
	forall j :: 0 <= j < i ==> arr[j] == a[j + middle + 1]
}

method RightLoopBody(arr: array<int>, a: array<int>, i: nat, middle: nat) 
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && i < arr.Length == a.Length - (middle + 1) && isValidIndex(a, middle) 
	requires Inv2(a, arr, middle, i)
	ensures Inv2(a, arr, middle, i+1)
	modifies arr
{
	LemmaArrIRight(arr, a, i, middle);
	arr[i] := a[i + middle + 1];
} 

lemma LemmaArrIRight(arr: array<int>, a: array<int>, i: nat, middle: nat)
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && i < arr.Length == a.Length - (middle + 1) && isValidIndex(a, middle) 
	requires Inv2(a, arr, middle, i)
	ensures arr[..i] + [a[i + middle + 1]] == a[middle+1 .. (i + middle + 2)]
{}

method MergeSort3(a: array<int>, left: array<int>, right: array<int>, middle: nat, i1: nat, i2: nat) returns (b: array<int>)
	requires isLeftArr(a, left, middle, i1) && isRightArr(a, right, middle, i2)
	requires left.Length + right.Length == a.Length
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
	decreases left.Length, right.Length
{
	// Sequential Composition
	var sortedL, sortedR := MergeSort3a(a, left, right, middle, i1, i2);
	b := MergeSort3b(a, left, right, sortedL, sortedR, middle);
}

method MergeSort3a(a: array<int>, left: array<int>, right: array<int>, middle: nat, i1: nat, i2: nat) returns (sortedL: array<int>, sortedR: array<int>)
	requires isLeftArr(a, left, middle, i1) && isRightArr(a, right, middle, i2)
	requires left.Length + right.Length == a.Length
	ensures isSorted(left, sortedL) && isSorted(right, sortedR)
	ensures sortedL.Length + sortedR.Length == a.Length
	decreases left.Length, right.Length
{
	// Sequential Composition
	sortedL := MergeSort(left);
	sortedR := MergeSort(right);
}

predicate isSorted(origin: array<int>, sortedArr: array<int>)
	reads origin, sortedArr
{
	sortedArr.Length == origin.Length && Sorted(sortedArr) && multiset(origin[..]) == multiset(sortedArr[..])
}

method {:verify true}  MergeSort3b(a: array<int>, left: array<int>, right: array<int>,sortedL: array<int>, sortedR: array<int>, middle: nat) returns(b: array<int>)
	requires isSorted(left, sortedL) && isSorted(right, sortedR)
	requires sortedL.Length + sortedR.Length == a.Length
	ensures Sorted(b) && multiset(b[..]) == multiset(sortedR[..])+multiset(sortedL[..])
{
		b := new int[a.Length];
		Merge(b, sortedL, sortedR);
}


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