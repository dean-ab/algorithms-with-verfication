predicate Sorted(a: array<int>)
	reads a
{
	forall i,j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
}

predicate SortedSequence(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

predicate isLeftArr(a: array<int>, left: array<int>, middle: nat)
	reads left, a
{
	a.Length >= 2 && middle == (a.Length - 1) / 2 && 0 < middle < a.Length &&
	left.Length == middle + 1 &&
	forall j :: 0 <= j < middle + 1 < left.Length ==> left[j] == a[j]
}

predicate isRightArr(a: array<int>, right: array<int>, middle: nat)
	reads right, a
{
	a.Length >= 2 && middle == (a.Length - 1) / 2 && 0 < middle < a.Length &&
	right.Length == a.Length - (middle + 1) &&
	forall j :: 0 <= j < (a.Length - (middle + 1)) < right.Length  ==> right[j] == a[j + (middle + 1)]
}

predicate isSorted(origin: array<int>, sortedArr: array<int>)
	reads origin, sortedArr
{
	sortedArr.Length == origin.Length && Sorted(sortedArr) && multiset(origin[..]) == multiset(sortedArr[..])
}

method {:verify false} MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
	decreases a.Length
	{
		if (a.Length < 2) {
			b := Assign1(a);
		} else {
			b := MergeSort1(a);
		}
	}

method {:verify false} Assign1 (a: array<int>) returns (b: array<int>)
	requires a.Length < 2
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
{
	LemmaS1(a);
	b := a;
}

lemma LemmaS1 (a: array<int>) 
	requires a.Length < 2
	ensures a.Length == a.Length && Sorted(a) && multiset(a[..]) == multiset(a[..])

{}

method {:verify false} MergeSort1 (a: array<int>) returns (b: array<int>)
	requires a.Length >= 2
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
{
	// Sequential Composition
	var middle := AssignMiddle(a);
	b := MergeSort2(a, middle);

}

method {:verify false} MergeSort2 (a: array<int>, middle: nat) returns (b: array<int>) 
	requires a.Length >= 2
	requires middle == (a.Length - 1) / 2 && 0 < middle < a.Length
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
{
	// Sequential Composition
	var left, right := Assign3Split(a, middle);
	b := MergeSort3(a, left, right, middle);
}

method {:verify false} AssignMiddle (a: array<int>) returns (m: nat) 
	requires a.Length >= 2
	ensures m == (a.Length - 1) / 2 && 0 <= m < a.Length
{
	LemmaS2(a);
	m := (a.Length - 1) / 2;
}

lemma LemmaS2 (a: array<int>) 
	requires a.Length >= 2
	ensures (a.Length - 1) / 2 == (a.Length - 1) / 2 && 0 <= (a.Length - 1) / 2 < a.Length 
{}


method {:verify false} Assign3Split (a: array<int>, middle: nat) returns (left: array<int>, right: array<int>)
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && 0 <= middle < a.Length
	ensures isLeftArr(a, left, middle)
	ensures isRightArr(a, right, middle)
{
	left := Assign3Left(a, middle);
	right :=  Assign3Right(a, middle);
}

method {:verify false} Assign3Left(a: array<int>, middle: nat) returns (arr: array<int>) 
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && 0 <= middle < a.Length
	ensures isLeftArr(a, arr, middle)
{
	var i := 0;
	arr := new int[middle+1];
	while (i < middle + 1) 
		decreases middle + 1 - i
		invariant forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j];
	{
		// I is increasing by one
		// arr[i] = a[i]
		LeftLoopBody(arr, a, i, middle); //following assignment
		i := i + 1;
	}
} 

method {:verify true} LeftLoopBody(arr: array<int>, a: array<int>, i: nat, middle: nat) 
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && middle >= 0 // Pre
	requires arr.Length == middle + 1
	requires i < middle + 1 && forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j]
	ensures forall j :: 0 <= j < i + 1  < arr.Length ==> arr[j] == a[j] // post cond of following assignment
	modifies arr
{
	LemmaArrI(arr, a, i, middle, a[i]);
	arr[i] := a[i];
} 

lemma  LemmaArrI(arr: array<int>, a: array<int>, i: nat, middle: nat, ai: int)
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && middle >= 0 // Pre
	requires arr.Length == middle + 1 >= 1
	requires i < middle + 1 && forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j]
	requires ai == a[i]
	ensures arr[..i] + [ai] == a[..i+1]
{}
method {:verify true}  Assign3Right(a: array<int>, middle: nat) returns (arr: array<int>) 
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && 0 < middle < a.Length
	ensures isRightArr(a, arr, middle)
{
	var i := 0;
	arr := new int[a.Length - (middle + 1)];
	while (i < a.Length - (middle + 1))
		decreases a.Length - (i + middle + 1)
		invariant forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j + middle + 1]
	{
		// I is increasing by one
		// arr[i] = a[i]
		RightLoopBody(arr, a, i, middle); // following assignment
		i := i + 1;
	}
} 

method {:verify true}  RightLoopBody(arr: array<int>, a: array<int>, i: nat, middle: nat) 
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && 0 <= middle < a.Length // Pre
	requires 0 <= i < a.Length - (middle + 1) // Guard
	requires forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j + middle + 1] // Inv
	requires arr.Length == a.Length - (middle + 1)
	ensures forall j :: 0 <= j < i + 1 < arr.Length ==> arr[j] == a[j + middle + 1] // post cond of following assignment
	modifies arr
{
	LemmaArrIRight(arr, a, i, middle, a[i + middle + 1]);
	arr[i] := a[i + middle + 1];
} 

lemma LemmaArrIRight(arr: array<int>, a: array<int>, i: nat, middle: nat, ai: int)
	requires a.Length >= 2 && middle == (a.Length - 1) / 2 && 0 <= middle < a.Length // Pre
	requires 0 <= i < a.Length - (middle + 1) // Guard
	requires ai == a[i + middle + 1] && arr.Length == a.Length - (middle + 1)
	requires forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j + middle + 1] // Inv
	ensures arr[..i] + [ai] == a[middle+1 .. (i + middle + 2)]
{}

method {:verify true}  MergeSort3(a: array<int>, left: array<int>, right: array<int>, middle: nat) returns(b: array<int>)
	requires isLeftArr(a, left, middle) && isRightArr(a, right, middle)
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
{
	//Sequantion composition
	var sortedL, sortedR := MergeSort3a(a, left, right, middle);
	b := MergeSort3b(a, left, right,sortedL, sortedR, middle);
}

method {:verify true}  MergeSort3a(a: array<int>, left: array<int>, right: array<int>, middle: nat) returns(sortedL: array<int>, sortedR: array<int>)
	requires isLeftArr(a, left, middle) && isRightArr(a, right, middle)
	ensures isSorted(left, sortedL) && isSorted(right, sortedR)
	
{
	//Sequantion composition
	sortedL := MergeSort(left);
	sortedR := MergeSort(right);
}

method {:verify true}  MergeSort3b(a: array<int>, left: array<int>, right: array<int>,sortedL: array<int>, sortedR: array<int>, middle: nat) returns(b: array<int>)
	requires isLeftArr(a, left, middle) && isRightArr(a, right, middle)
	requires isSorted(left, sortedL) && isSorted(right, sortedR)
	{
		b := new int[a.Length];
		Merge(b, sortedL, sortedR);
	}


method {:verify true}  Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
	{
		var k,l,r := 0,0,0;
		k,l,r := MergeWhileLoop(b, c, d, k, l, r);
		assert ((l == c.Length && r < d.Length) || (l < c.Length && r == d.Length));
		MergeRest(b, c, d, k, l, r);
	}

predicate CrossSorted(b: array<int>, c: array<int>, d: array<int>, k: nat, l: nat, r: nat) 
	reads b, c, d
{
	forall i, n, m :: (0 <= i < k < b.Length && l <= n < c.Length && r <= m < d.Length) ==> b[i] <= c[n] && b[i] <= d[m] // Sorted(b[.. k])
}
predicate MergeInv(b: array<int>, c: array<int>, d: array<int>, k: nat, l: nat, r: nat) 
	reads b, c, d
{
	 0 <= k <= b.Length && 0 <= l <= c.Length && 0 <= r <= d.Length &&  k == l + r && 
	 multiset(b[..k]) == multiset(c[..l] + d[..r]) && CrossSorted(b,c,d,k,l,r) &&
	 forall i,j :: 0 <= j < i < k ==> b[j] <= b[i] // Sorted(b[.. k])
}

predicate areValidIndices (b: array<int>, c: array<int>, d: array<int>, k: int, l: int, r: int) 
{
	0 <= k < b.Length && 0 <= l < c.Length && 0 <= r < d.Length 	
}
method {:verify false}  MergeWhileLoop(b: array<int>, c: array<int>, d: array<int>, k0: nat, l0: nat, r0: nat) returns(k: nat, l: nat, r: nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d) 
	requires k0 == 0 && l0 == 0 && r0 == 0
	ensures MergeInv(b,c,d,k,l,r) 
	ensures (l == c.Length && r < d.Length) || (l < c.Length && r == d.Length)
	modifies b
{
	k, l, r := k0, l0, r0;
	while (r < d.Length && l < c.Length && k < b.Length)
		decreases b.Length - k
		invariant MergeInv(b,c,d,k,l,r)
	{
		// Following Assignment k
		k,l,r := MergeLoopBody(b, c, d, k, l, r);
		k := k + 1;
	}
}

method {:verify false} MergeLoopBody(b: array<int>, c: array<int>, d: array<int>, k0: nat, l0: nat, r0: nat) returns(k: nat, l: nat, r: nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d) 
	requires MergeInv(b,c,d,k0,l0,r0) && k0 < b.Length && l0 < c.Length && r0 < d.Length  // Inv & Guard
	ensures MergeInv(b,c,d,k+1,l,r) && 0 <= l <= c.Length && r0 + l0 < r + l
{
	k, l, r := k0, l0, r0;
	if (c[l] <= d[r]) {
		// Following Assignment l
		MergeLoopBody1(b,c,d,k,l,r);
		l := l+1;
	} else {
		// Following Assignment r
		MergeLoopBody2(b,c,d,k,l,r);
		r := r+1;
	}
}

method {:verify true}  MergeLoopBody1(b: array<int>, c: array<int>, d: array<int>, k0: nat, l0: nat, r0: nat) 
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d) 
	requires MergeInv(b,c,d,k0,l0,r0) && k0 < b.Length && l0 < c.Length && r0 < d.Length  // Inv & Guard
	requires c[l0] <= d[r0] // If Test
	ensures MergeInv(b,c,d,k0+1,l0+1,r0)
	modifies b
{
	// Following assignment k0+1
	LemmaLB1(b,c,d,k0+1,l0+1,r0);
	b[k0] := c[l0];
}

lemma LemmaLB1(b: array<int>, c: array<int>, d: array<int>, k: nat, l: nat, r: nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d) 
	requires areValidIndices(b,c,d,k-1,l-1,r) && MergeInv(b,c,d,k-1,l-1,r) 
	requires c[l-1] <= d[r] // If Test
	// Modify MergeInv
	ensures 0 <= k <= b.Length && 0 <= l <= c.Length && 0 <= r <= d.Length &&  k == l + r && 
	 multiset(b[..k-1] + [c[l-1]]) == multiset(c[..l] + d[..r]) && 
	 forall i, n, m :: (0 <= i < k - 1 < b.Length && l <= n < c.Length && r <= m < d.Length) ==> b[i] <= c[n] && b[i] <= d[m] && c[l-1] <= d[m] // Sorted(b[.. k])  
	ensures forall i,j :: 0 <= j < i < k - 1 ==> b[j] <= b[i] && b[j] <= c[l-1] // Sorted(b[.. k])
{}

method {:verify true}  MergeLoopBody2(b: array<int>, c: array<int>, d: array<int>, k0: nat, l0: nat, r0: nat) 
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d) 
	requires MergeInv(b,c,d,k0,l0,r0) && k0 < b.Length && l0 < c.Length && r0 < d.Length  // Inv & Guard
	requires c[l0] > d[r0] // !If Test
	ensures MergeInv(b,c,d,k0+1,l0,r0+1)
	modifies b
{
	// Following assignment k0+1
	LemmaLB2(b,c,d,k0+1,l0,r0+1);
	b[k0] := d[r0];
}

lemma LemmaLB2(b: array<int>, c: array<int>, d: array<int>, k: nat, l: nat, r: nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d) 
	requires areValidIndices(b,c,d,k-1,l,r-1) && MergeInv(b,c,d,k-1,l,r-1) 
	requires c[l] > d[r-1] // !If Test
	// Modify MergeInv
	ensures 0 <= k <= b.Length && 0 <= l <= c.Length && 0 <= r <= d.Length &&  k == l + r && 
	 multiset(b[..k-1] + [d[r-1]]) == multiset(c[..l] + d[..r]) && 
	 forall i, n, m :: (0 <= i < k - 1 < b.Length && l <= n < c.Length && r <= m < d.Length) ==> b[i] <= c[n] && b[i] <= d[m] && d[r-1] <= c[n] // Sorted(b[.. k])  
	ensures forall i,j :: 0 <= j < i < k - 1 ==> b[j] <= b[i] && b[j] <= d[r-1] // Sorted(b[.. k])
{}

method {:verify true}  MergeRest(b: array<int>, c: array<int>, d: array<int>, k: nat, l: nat, r: nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	requires MergeInv(b,c,d,k,l,r) && ((l == c.Length && r < d.Length) || (l < c.Length && r == d.Length))
	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b 
{
	if (l == c.Length) {
		MergeRest1(b,c,d,k,l,r);
	} else {
		MergeRest2(b,c,d,k,l,r);
	}
}

predicate MergeRestInv(b: array<int>, c: array<int>, d: array<int>, k: nat, l: nat, r: nat) 
	reads b, c, d
{
	 0 <= k <= b.Length && 0 <= l <= c.Length && 0 <= r <= d.Length &&  k == l + r && 
	 multiset(b[..k]) == multiset(c[..l] + d[..r]) && 
	 forall i,j :: 0 <= j < i < k ==> b[j] <= b[i] // Sorted(b[.. k])
}

predicate CrossSortedRest1(b: array<int>, arr: array<int>, k: nat, index: nat) 
	reads b, arr
{
	forall i, n :: (0 <= i < k < b.Length && index <= n < arr.Length ) ==> b[i] <= arr[n] // Sorted(b[.. k])
}
method {:verify true}  MergeRest1(b: array<int>, c: array<int>, d: array<int>, k: nat, l: nat, r: nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	requires MergeInv(b,c,d,k,l,r)
	requires forall j, m :: 0 <= j < k && r <= m < d.Length ==> b[j] <= d[m]
	requires ((l == c.Length && r < d.Length) || (l < c.Length && r == d.Length)) && l == c.Length//r < d.Length // Guard
	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..]) 
	modifies b
{
	var r1: nat, k1: nat := r, k;
	assert r1 < d.Length;
	assert 	forall i, n, m :: (0 <= i < k < b.Length && l <= n < c.Length && r <= m < d.Length) ==> b[i] <= c[n] && b[i] <= d[m]; // Sorted(b[.. k])

	while (k1 < b.Length && r1 < d.Length) 
		decreases b.Length - k1
		invariant MergeRestInv(b,c,d,k1,l,r1) 
	{
		assert 	forall i, n, m :: (0 <= i < k < b.Length && l <= n < c.Length && r <= m < d.Length) ==> b[i] <= c[n] && b[i] <= d[m]; // Sorted(b[.. k])

		assert MergeRestInv(b,c,d,k1,l,r1);

		assert r1 < d.Length;
		b[k1] := d[r1];
		r1 := r1 + 1;
		k1 := k1 + 1;


		assert 0 <= k1 <= b.Length;
		assert 0 <= l <= c.Length;
		assert 0 <= r1 <= d.Length;
		assert  k1 == l + r1;
	 	assert multiset(b[..k1]) == multiset(c[..l] + d[..r1]);
	 	assert forall i,j :: 0 <= j < i < k1 < b.Length ==> b[j] <= b[i]; // Sorted(b[.. k])
	}
}

method {:verify true}  MergeRest2(b: array<int>, c: array<int>, d: array<int>, k: nat, l: nat, r: nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	requires MergeInv(b,c,d,k,l,r)
	requires l < c.Length // Guard
	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..]) 
	modifies b
{
	var l1: nat, k1: nat := l, k;
	assert l1 < d.Length;
	while (k1 < b.Length && l1 < c.Length) 
		decreases b.Length - k1
		invariant MergeRestInv(b,c,d,k1,l1,r) 
	{
		b[k1] := c[l1];
		l1 := l1 + 1;
		k1 := k1 + 1;
		// assert 0 <= k1 <= b.Length;
		// assert 0 <= l <= c.Length;
		// assert 0 <= r1 <= d.Length;
		// assert  k1 == l + r1;
	 	// assert multiset(b[..k1]) == multiset(c[..l] + d[..r1]);
	}
}

method Main() {
	var a := new int[6];
	a[0] := 10;
	a[1] := 39;
	a[2] := 1;
	a[3] := 0;
	a[4] := -1;
	a[5] := 2;
	var q0 := a[..];
	// assert q0 == [4,8,6];
	a := MergeSort(a);
	// assert a.Length == |q0| && multiset(a[..]) == multiset(q0);
	print "the sorted version of [4, 8, 6] is ";
	print a[..];
	// assert Sorted(a);
	// assert a[..] == [4,6,8];
}


