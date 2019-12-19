In this repository we prove correctness of quickSort. In this file we will describe the common ideas in the file and how our definition works.
We want to define quicksort as: 
```
Fixpoint quicksort (l: list nat) :=
    match l with
    	| nil => nil
    	| h :: t => (quicksort (filter_lte h t)) ++ h :: (quicksort (filter_gt h t))
    end.
```
 
This is a correct mathematical definition of quicksort however Coq doesn't accept this definition. Coq can only work with finite fixpoints. No infinite structures are allowed, this is usually not a problem since Coq can identify termination of most fixpoints. Coq notices that if we have (a set of) strictly decreasing parameters in a recursive call then the recursion terminates. In the definition shown above we recurse on (quicksort (filter_lte h t)) trivially (filter_lte h t) is strictly smaller then l, however Coq does not know this. Coq therefore does not accept our definition. We can solve this by adding a strictly decreasing parameter of type:
```
Inductive qs_tree : list nat -> Type :=
| qs_ leaf : qs_concat nil
| qs_ node : forall ( x: nat) (xs: list nat), 
  qs_tree (filter (fun y => leb y  x) (xs)) -> 
  qs_tree (filter (fun y => negb (leb y x)) (xs)) -> 
    qs_tree (cons x xs).
```
While this type looks very impressive it can be seen as the recursion tree of quicksort. You can look at the leaves of the tree (qs_leaf) as a call (quicksort nil). You can look as the nodes in the tree (qs_node) as a call (quicksort (x:xs)) now the left subtree contains  qs_tree (filter (fun y => leb y  x) (xs))  and the right sub tree contains filter (fun y => negb (leb y x)) (xs), these are indeed just the calls quicksort (x:xs) makes to recurse. 

We could now define a quicksort function with one more parameter:

```
Fixpoint qs_helper (l : list nat) (q : qs_tree l) {struct q} : list nat :=
  match q with
  | qs_tree_base => nil
  | qs_tree_step x xs q0 q1 =>
      (qs_helper (filter (fun y : nat => leb y x) xs) q0) ++ (x ::
        (qs_helper (filter (fun y : nat => negb (leb y x)) xs) q1))
  end.
```

Here tree is a finite structure which is strictly decreasing and finite so coq understands the recursion terminates. Next we need to create the recursion tree. We need to create an opaque lemma (which you can run using simpl and compute) to create the recursion tree for any given list of natural numbers xl.
```
Lemma create_qs_tree: forall (l : list nat), (qs_tree l).
Proof.
...
Defined.
```

Now we can define quicksort as:
```
Definition quickSort (ls :list nat) := qs_helper ls (create_qs_tree ls).
```

We can now prove properties about quickSort. We can unfold quickSort and use induction on the recursion tree argument to prove correctness using induction. We prove two major lemmas:

```
Lemma qs_In_equiv : forall (xs : list nat) (x : nat), 
  (In x (quickSort xs)) <-> ( In x xs).
```

```
Lemma qs_sorted : forall (xs: list nat),
  Sorted le (quickSort xs).
```











