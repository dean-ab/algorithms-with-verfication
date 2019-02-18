datatype Tree = Empty | Node(int,Tree,Tree)

method Main() {
	var tree := BuildBST([0, 3, 2, -1, 1]);
	PrintTreeNumbersInorder(tree, 0);
}

method PrintTreeNumbersInorder(t: Tree, i: nat)
    decreases t, i
{
	match t {
		case Empty =>
		case Node(n, l, r) =>
			PrintTreeNumbersInorder(r, i + 1);
			var j := 0;
			while (j < i) 
                decreases i - j
            {
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
    decreases t
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

method BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
	// Contact Frame + Introducing Local Variable
	var i, tree := 0, Empty;
	t := BuildBST1(q, tree, i);

    StrengthenPostLemma(q, t); //Strengthen Postcondition
}

lemma StrengthenPostLemma(q: seq<int>, t: Tree)
    requires BSTpred(q, t, |q|)
    ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{}

predicate BSTpred(q: seq<int>, t: Tree, i: nat) {
    BST(t) && 0 <= i <= |q| && NoDuplicates(q) &&
    NumbersInTree(t) == NumbersInSequence(q[..i])
}

method BuildBST1(q: seq<int>, oldT: Tree, i: nat) returns (t: Tree) 
    requires BSTpred(q, oldT, i)
    ensures BSTpred(q, t, |q|)
	decreases |q|-i, 1
{
	// Alternation
	if (i == |q|) {
        LemmaFullTree(q,oldT,|q|); //Assignment
		t := oldT;
	} else { 
		t := BuildBST2(q,oldT,i);
	}
}

lemma LemmaFullTree(q: seq<int>, t: Tree, i: nat)
    requires BSTpred(q,t,i) && i == |q|
    ensures BSTpred(q,t,i)
{} 

method BuildBST2(q: seq<int>, oldT: Tree, i: nat) returns (t: Tree)
	requires i != |q| && BSTpred(q, oldT, i)
    ensures BSTpred(q, t, |q|)
	decreases |q|-i, 0
{
	// Sequantial Composition + Introducing Local Variable
	var extendTree := InsertBST(oldT, q[i]);
	t := BuildBST1(q, extendTree, i+1);
}

method InsertBST(oldT: Tree, x: int) returns (t: Tree)
	requires BST(oldT) && x !in NumbersInTree(oldT)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(oldT)+{x}
	decreases oldT, 2
{
    // Alternation
	match oldT {
		case Empty => 
            LemmaEmptyBST(oldT,x); //Assignment
            t := Node(x, Empty, Empty);
		case Node(val, left, right) => 
            t := InsertBST1(oldT, x, val, left, right);
	}
}

lemma LemmaEmptyBST(t: Tree, x: int)
	requires BST(t) && x !in NumbersInTree(t) && t == Empty
	ensures BST(Node(x, Empty, Empty))
    ensures NumbersInTree(Node(x, Empty, Empty)) == NumbersInTree(t)+{x}
{}

method InsertBST1(oldT: Tree, x: int, val: int, lT: Tree, rT: Tree) returns (t: Tree)
    requires BST(oldT) && x !in NumbersInTree(oldT)
	requires oldT == Node(val,lT,rT)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(oldT)+{x}
	decreases oldT, 1
{
    // Alternation
	if (x < val) {
		t := InsertBST1Left(oldT, x, val, lT, rT);
	} else {
		t := InsertBST1Right(oldT, x, val, lT, rT);
	}
}

method InsertBST1Left(oldT: Tree, x: int, val: int, lT: Tree, rT: Tree) returns (t: Tree)
    requires BST(oldT) && x !in NumbersInTree(oldT) && oldT == Node(val,lT,rT)
	requires x < val //Guard
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(oldT)+{x}
	decreases oldT, 0
{
	assert BST(lT) by {LemmaBinarySearchSubtree(val, lT, rT);}
	var newL := InsertBST(lT, x);

	LemmaInsertLeftSub(oldT,val,lT,rT,newL,x);
	t := Node(val, newL, rT);
}

lemma LemmaInsertLeftSub(t: Tree, n: int, lT: Tree, rT: Tree, newL: Tree, x:int)
    requires BST(t) && x !in NumbersInTree(t) && t == Node(n,lT,rT)
	requires BST(lT) && x < n //Guard
	requires NumbersInTree(newL) == NumbersInTree(lT)+{x} && BST(newL)
	ensures BST(Node(n, newL, rT))
    ensures NumbersInTree(Node(n, newL, rT)) == NumbersInTree(t)+{x}
{
	var qL, qR, qNewL := Inorder(lT), [n] + Inorder(rT), Inorder(newL);
	var qOld, q := qL + qR, qNewL + qR;
    var NITnewL := NumbersInTree(newL);

    assert q == Inorder(Node(n, newL, rT));
    assert Ascending(qOld) by {assert qL + [n] + qR[1..] == qOld;}
    assert Ascending(qR) by {LemmaAscendingSubsequence(qOld, qR, |qL|);}
	assert forall i :: 0 < i < |qR| ==> qR[i] > n by {
        assert qR[0] == n &&
		forall j,k :: 0 < j < k < |qR| ==> 
        n < qR[j] < qR[k];
	}

    forall i | 0 <= i < |qNewL| ensures qNewL[i] < n {
        assert forall i :: 0 <= i < |qL| ==> qL[i] < n by {
        assert n == qOld[|qL|] && qL == qOld[..|qL|];
        }
		assert forall j :: j in NITnewL && j != x ==> j in qL;
        assert qNewL[i] in qL || qNewL[i] == x;
    }
}

method InsertBST1Right(oldT: Tree, x: int, val: int, lT: Tree, rT: Tree) returns (t: Tree)
    requires BST(oldT) && x !in NumbersInTree(oldT) && oldT == Node(val,lT,rT)
	requires x > val //Guard
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(oldT)+{x}
	decreases oldT, 0
{
	assert BST(rT) by {LemmaBinarySearchSubtree(val, lT, rT);}
	var newR := InsertBST(rT, x);

	LemmaInsertRightSub(oldT,val,lT,rT,newR,x);
	t := Node(val, lT, newR);
}

lemma LemmaInsertRightSub(t: Tree, n: int, lT: Tree, rT: Tree, newR: Tree, x:int)
    requires BST(t) && x !in NumbersInTree(t) && t == Node(n,lT,rT)
	requires BST(rT) && x > n //Guard
	requires NumbersInTree(newR) == NumbersInTree(rT)+{x} && BST(newR)
	ensures BST(Node(n, lT, newR))
    ensures NumbersInTree(Node(n, lT, newR)) == NumbersInTree(t)+{x}
{
    var qL, qR, qNewR := Inorder(lT) + [n], Inorder(rT), Inorder(newR);
	var qOld, q := qL + qR, qL + qNewR;
    var NITnewR := NumbersInTree(newR);

    assert q == Inorder(Node(n, lT, newR));
    assert Ascending(qOld);
    assert Ascending(qL) by {LemmaAscendingSubsequence(qOld, qL, 0);}
	assert forall i :: 0 <= i < |qL| ==> qL[i] <= n by {
        assert qL[|qL|-1] == n &&
		forall j,k :: 0 < j < k < |qL|-1 ==> 
        qL[j] < qL[k] < n;
	}

    forall i | 0 <= i < |qNewR| ensures qNewR[i] > n {
        assert forall i :: 0 <= i < |qR| ==> qR[i] > n by {
        assert n == qOld[|qL|-1] && qR == qOld[|qL|..];
        }
		assert forall j :: j in NITnewR && j != x ==> j in qR;
        assert qNewR[i] in qR || qNewR[i] == x;
    }
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

lemma LemmaAscendingSubsequence(q1: seq<int>, q2: seq<int>, i: nat)
	requires i <= |q1|-|q2| && q2 == q1[i..i+|q2|]
	requires Ascending(q1)
	ensures Ascending(q2)
{}