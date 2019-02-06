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
	{
		if (a.Length < 2) {
			b := Assign1(a);
		} else {
			b := MergeSort1(a);
		}
	}

method Assign1 (a: array<int>) returns (b: array<int>)
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

method MergeSort1 (a: array<int>) returns (b: array<int>)
	requires a.Length >= 2
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
{
	// Sequential Composition
	var middle := AssignMiddle(a);
	b := MergeSort2(a, middle);

}

method MergeSort2 (a: array<int>, middle: nat) returns (b: array<int>) 
	requires a.Length >= 2
	requires middle == a.Length / 2 && 0 < middle < a.Length
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
{
	// Sequential Composition
	
	var left, right := Assign3Split(a, middle);
	// b := MergeSort3(a, left, right);
}

method AssignMiddle (a: array<int>) returns (m: nat) 
	requires a.Length >= 2
	ensures m == a.Length / 2 && 0 < m < a.Length
{
	LemmaS2(a);
	m := a.Length / 2;
}

lemma LemmaS2 (a: array<int>) 
	requires a.Length >= 2
	ensures a.Length / 2 == a.Length / 2 && 0 < a.Length / 2 < a.Length 
{
}


method Assign3Split(a: array<int>, middle: nat) returns (left: array<int>, right: array<int>) 
	requires a.Length >= 2 && middle == a.Length / 2 && 0 < middle < a.Length
	ensures forall j :: 0 <= j < middle + 1 < left.Length ==> left[j] == a[j]
	ensures forall j :: 0 <= j < (a.Length - (middle + 1)) < right.Length  ==> right[j] == a[j + (middle + 1)]
{
	left := Assign3Left(a, middle);
	right :=  Assign3Right(a, middle);
}

method Assign3Left(a: array<int>, middle: nat) returns (arr: array<int>) 
	requires a.Length >= 2 && middle == a.Length / 2 && 0 < middle < a.Length
	ensures forall j :: 0 <= j < middle + 1 < arr.Length ==> arr[j] == a[j]
{
	var i := 0;
	arr := new int[middle+1];
	while (i < middle + 1) 
		decreases middle + 1 - i
		invariant forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j];
	{
		// I is increasing by one
		// arr[i] = a[i]
		LeftLoopBody(arr, a, i, middle);
		LemmaI1(arr, a, i+1, middle);
		i := i + 1;
	}
} 

method LeftLoopBody(arr: array<int>, a: array<int>, i: nat, middle: nat) 
	requires a.Length >= 2 && middle == a.Length / 2 && middle > 0 // Pre
	requires arr.Length == middle + 1
	requires i < middle + 1 && forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j]
	ensures forall j :: 0 <= j <= i  < arr.Length ==> arr[j] == a[j]
	modifies arr
{
	LemmaArrI(arr, a, i, middle, a[i]);
	arr[i] := a[i];
} 

lemma  LemmaArrI(arr: array<int>, a: array<int>, i: nat, middle: nat, ai: int)
	requires a.Length >= 2 && middle == a.Length / 2 && middle > 0 // Pre
	requires arr.Length == middle + 1 >= 2
	requires i < middle + 1 && forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j]
	requires ai == a[i]
	ensures arr[..i] + [ai] == a[..i+1]
{}

lemma LemmaI1 (arr: array<int>, a: array<int>, i: nat, middle: nat)
	requires a.Length >= 2 && middle == a.Length / 2 && 0 < middle < a.Length
	requires arr.Length == middle + 1 && i-1 < middle + 1
	requires forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j] //post of LeftLoopBody
	ensures forall j :: 0 <= j < i < arr.Length < a.Length ==> arr[j] == a[j]
{}

method Assign3Right(a: array<int>, middle: nat) returns (arr: array<int>) 
	requires a.Length >= 2 && middle == a.Length / 2 && 0 < middle < a.Length
	ensures forall j :: 0 <= j < (a.Length - (middle + 1)) < arr.Length  ==> arr[j] == a[j + (middle + 1)]
{
	var i := 0;
	arr := new int[a.Length - (middle + 1)];
	while (i < a.Length - (middle + 1))
		decreases a.Length - (i + middle + 1)
		invariant forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j + middle + 1]
	{
		// I is increasing by one
		// arr[i] = a[i]
		RightLoopBody(arr, a, i, middle);
		LemmaI2(arr, a, i+1, middle);
		i := i + 1;
	}
} 

method RightLoopBody(arr: array<int>, a: array<int>, i: nat, middle: nat) 
	requires a.Length >= 2 && middle == a.Length / 2 && 0 < middle < a.Length // Pre
	requires 0 <= i < a.Length - (middle + 1) // Guard
	requires forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j + middle + 1] // Inv
	requires arr.Length == a.Length - (middle + 1)
	ensures forall j :: 0 <= j <= i < arr.Length ==> arr[j] == a[j + middle + 1]
	modifies arr
{
	LemmaArrIRight(arr, a, i, middle, a[i + middle + 1]);
	arr[i] := a[i + middle + 1];
} 

lemma LemmaArrIRight(arr: array<int>, a: array<int>, i: nat, middle: nat, ai: int)
	requires a.Length >= 2 && middle == a.Length / 2 && 0 < middle < a.Length // Pre
	requires 0 <= i < a.Length - (middle + 1) // Guard
	requires ai == a[i + middle + 1] && arr.Length == a.Length - (middle + 1)
	requires forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j + middle + 1] // Inv
	ensures arr[..i] + [ai] == a[middle+1 .. (i + middle + 2)]
{}

lemma LemmaI2 (arr: array<int>, a: array<int>, i: nat, middle: nat)
	requires a.Length >= 2 && middle == a.Length / 2 && 0 < middle < a.Length
	requires i-1 < a.Length - (middle + 1) // Guard
	requires forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j + middle + 1] //post of RighttLoopBody
	ensures forall j :: 0 <= j < i < arr.Length ==> arr[j] == a[j + middle + 1]
{}


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
