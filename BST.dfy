datatype Tree = Empty | Node(int,Tree,Tree)

method Main() {
	var tree := BuildBST([0, 3, 2, -1, 1]);
	PrintTreeNumbersInorder(tree, 0);
}

method PrintTreeNumbersInorder(t: Tree, i: nat)
{
	match t {
		case Empty =>
		case Node(n, l, r) =>
			PrintTreeNumbersInorder(r, i + 1);
			var j := 0;
			while (j < i) {
				print "\t";
				j := j + 1;
			}
			print n;
			print "\n";
			PrintTreeNumbersInorder(l, i + 1);
	}
}

function NumbersInTree(t: Tree): set<int>
{
	NumbersInSequence(Inorder(t))
}

function NumbersInSequence(q: seq<int>): set<int>
{
	set x | x in q
}

predicate BST(t: Tree)
{
	Ascending(Inorder(t))
}

function Inorder(t: Tree): seq<int>
{
	match t {
		case Empty => []
		case Node(n',nt1,nt2) => Inorder(nt1)+[n']+Inorder(nt2)
	}
}

predicate Ascending(q: seq<int>)
{
	forall i,j :: 0 <= i < j < |q| ==> q[i] < q[j]
}

predicate NoDuplicates(q: seq<int>) { forall i,j :: 0 <= i < j < |q| ==> q[i] != q[j] }

predicate isValidIndex(q: seq<int>, index: nat) 
{
	0 <= index <= |q|
}

method {:verify true} BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
	// Contact Frame + Introducing Local Variable
	var i, tree := 0, Empty;
	t := BuildBST1(q, tree, i);
}

method {:verify true} BuildBST1(q: seq<int>, tree: Tree, i: nat) returns (t: Tree) 
	requires NoDuplicates(q)
	requires isValidIndex(q, i) && BST(tree)
	requires NumbersInTree(tree) == NumbersInSequence(q[..i])
	ensures isValidIndex(q, i) && BST(t) && NumbersInTree(t) == NumbersInSequence(q)
	decreases |q|-i, 1
{
	// Alternation
	if (i == |q|) {
		t := BuildBST1a(q,tree,i);
	} else { 
		t := BuildBST1b(q,tree,i);
	}
}

method {:verify true} BuildBST1a(q: seq<int>, tree: Tree, i: nat) returns (t: Tree)
	requires NoDuplicates(q)
	requires isValidIndex(q, i) && BST(tree)
	requires i == |q|
	requires NumbersInTree(tree) == NumbersInSequence(q[..i])
	ensures isValidIndex(q, i) && BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
	// Assignment
	Lemma1(q,tree,i);
	t := tree;
} 

method {:verify true} BuildBST1b(q: seq<int>, tree: Tree, i: nat) returns (t: Tree)
	requires NoDuplicates(q)
	requires isValidIndex(q, i) && BST(tree)
	requires i != |q|
	requires NumbersInTree(tree) == NumbersInSequence(q[..i])
	ensures isValidIndex(q, i) && BST(t) && NumbersInTree(t) == NumbersInSequence(q)
	decreases |q|-i, 0
{
	// Sequantial Composition + Introducing Local Variable
	var extendTree := InsertBST(tree, q[i]);
	t := BuildBST1(q, extendTree, i+1);
}


lemma Lemma1(q: seq<int>, tree: Tree, i: nat)
	requires NoDuplicates(q)
	requires isValidIndex(q, i) && BST(tree)
	requires i == |q|
	requires NumbersInTree(tree) == NumbersInSequence(q[..i])
	ensures isValidIndex(q, i) && BST(tree) && NumbersInTree(tree) == NumbersInSequence(q)
{}

method {:verify true} InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
	decreases t0, 2
{
	match t0 {
		case Empty => t := EmptyBST(t0, x);
		case Node(val, left, right) => t := InsertBST1(t0, x, val, left, right);
	}
}

method {:verify true} EmptyBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0) && t0 == Empty
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
{
	LemmaEmptyBST(t0,x);
	t := Node(x, Empty, Empty);
}

lemma LemmaEmptyBST(t: Tree, x: int)
	requires BST(t) && x !in NumbersInTree(t)  && t == Empty
	ensures BST(Node(x, Empty, Empty)) && NumbersInTree(Node(x, Empty, Empty)) == NumbersInTree(t)+{x}
{}

method {:verify true} InsertBST1(t0: Tree, x: int, val: int, left: Tree, right: Tree) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0) && t0 == Node(val,left,right)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
	decreases t0, 1
{
	if (x < val) {
		t := InsertBST1Left(t0, x, val, left, right);
	} else {
		t := InsertBST1Right(t0, x, val, left, right);
	}
}

method {:verify true} InsertBST1Left(t0: Tree, x: int, val: int, left: Tree, right: Tree) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0) && t0 == Node(val,left,right)
	requires x < val
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
	decreases t0, 0
{
	LemmaBinarySearchSubtree(val,left,right);
	var l := InsertBST(left, x);
	LemmaBinarySearchTreeLeft(t0,val,l,right, left, x);
	t := Node(val, l, right);
}

method {:verify true} InsertBST1Right(t0: Tree, x: int, val: int, left: Tree, right: Tree) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0) && t0 == Node(val,left,right)
	requires x > val
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
	decreases t0, 0
{
	LemmaBinarySearchSubtree(val,left,right);
	var r := InsertBST(right, x);
	LemmaBinarySearchTreeRight(t0,val,left,right, r, x);
	t := Node(val, left, r);
}

lemma LemmaBinarySearchSubtree(n: int, left: Tree, right: Tree)
	requires BST(Node(n, left, right))
	ensures BST(left) && BST(right)
{
	assert Ascending(Inorder(Node(n, left, right)));
	var qleft, qright := Inorder(left), Inorder(right);
	var q := qleft+[n]+qright;
	assert q == Inorder(Node(n, left, right));
	assert Ascending(qleft+[n]+qright);
	assert Ascending(qleft) by { LemmaAscendingSubsequence(q, qleft, 0); }
	assert Ascending(qright) by { LemmaAscendingSubsequence(q, qright, |qleft|+1); }
}

lemma {:verify true} LemmaBinarySearchTreeLeft(t: Tree, n: int, left: Tree, right: Tree, left0: Tree, x:int)
	requires BST(left0) && BST(right) && BST(t) && t == Node(n, left0, right)
	requires BST(left) && NumbersInTree(left) == NumbersInTree(left0)+{x} && x < n 
	ensures BST(Node(n, left, right))
{
	var inorderLeft := Inorder(left0);
	var inorderRight := Inorder(right);
	var newLeftInorder := Inorder(left);
	var qOld := inorderLeft + [n] + inorderRight;
	var q := newLeftInorder + [n] + inorderRight;

	assert Ascending(q) == BST(Node(n, left, right));

	assert Ascending(q) by {
		assert Ascending(newLeftInorder);
		assert Ascending(inorderRight);
		assert Ascending(inorderLeft);
		assert Ascending(qOld) && forall j :: j in inorderLeft ==> j < n;
		forall i | i in NumbersInSequence(newLeftInorder) ensures i < n {
			if (i == x) {
				assert i < n;
			} else if (i < x) {
				assert i < x < n;
			} if (i > x) {
				var shit := inorderLeft + [n];
				assert Ascending(shit) by { LemmaAscendingSubsequence(qOld, inorderLeft + [n], 0); }
				assert shit == Inorder(Node(n, left0, Empty));
				assert i in shit && Ascending(shit);
			}
		}
	}
}

lemma {:verify true} LemmaBinarySearchTreeRight(t: Tree, n: int, left: Tree, right0: Tree, right: Tree, x:int)
	requires BST(left) && BST(right0) && BST(t) && t == Node(n, left, right0)
	requires BST(right) && NumbersInTree(right) == NumbersInTree(right0)+{x} && x > n 
	ensures BST(Node(n, left, right))
{}

lemma LemmaAscendingSubsequence(q1: seq<int>, q2: seq<int>, i: nat)
	requires i <= |q1|-|q2| && q2 == q1[i..i+|q2|]
	requires Ascending(q1)
	ensures Ascending(q2)
{}
