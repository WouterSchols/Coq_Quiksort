Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Structures.OrdersFacts.
Require Import Omega.
Require Import Coq.Logic.ClassicalFacts.

(*The recursion tree for quickSort*)
Inductive qs_tree : list nat -> Type :=
| qs_tree_base : qs_tree nil
| qs_tree_step : forall ( x: nat) (xs: list nat), 
  qs_tree (filter (fun y => leb y  x) (xs)) -> 
  qs_tree (filter (fun y => negb (leb y x)) (xs)) -> 
    qs_tree (cons x xs).

(*The fixpoint which evaluates a recursion tree*)
Fixpoint qs_helper (l : list nat) (q : qs_tree l) {struct q} : list nat :=
  match q with
  | qs_tree_base => nil
  | qs_tree_step x xs q0 q1 =>
      (qs_helper (filter (fun y : nat => leb y x) xs) q0) ++ (x ::
        (qs_helper (filter (fun y : nat => negb (leb y x)) xs) q1))
  end.

Require Import Coq.Sorting.Sorted.

(*Create the recursion tree for a given list*)
  (*Redefine lemmas from libraries to be opaque*)
Lemma leb_correct : forall m n:nat, m <= n -> leb m n = true.
Proof.
  induction m as [| m IHm]. trivial.
  destruct n. intro H. elim (le_Sn_O _ H).
  intros. simpl in |- *. apply IHm. apply le_S_n. assumption.
Defined.

Lemma leb_correct_conv : forall m n:nat, m < n -> leb n m = false.
Proof.
  intros.
  generalize (leb_complete n m).
  destruct (leb n m); auto.
  intros.
  elim (lt_irrefl _ (lt_le_trans _ _ _ H (H0 (refl_equal true)))).
Defined.

Lemma not_true_is_false : forall b:bool, b <> true -> b = false.
destruct b.
intros.
red in H; elim H.
reflexivity.
intros abs.
reflexivity.
Defined.

Lemma gt_leb_conv: forall (a: nat) (a0 : nat),(a > a0) -> (a0 <= a).
Proof.
intros.
intuition.
Defined.

  (*New facts about filters*)
Lemma filter_commutative: forall (xs : list nat) (f1 : nat -> bool) (f2 : nat -> bool),
   (filter f2 (filter f1 xs))
= (filter f1 (filter f2 xs)).
Proof.
intros.
induction xs.
simpl. (*base case*)
intuition.
simpl. (*step*)
destruct (bool_dec (f1 a) true).
destruct (bool_dec (f2 a) true).
rewrite e.
rewrite e0.
simpl.
rewrite e.
rewrite e0.
rewrite IHxs.
intuition. (*case f1,!f2*)
apply not_true_is_false in n.
rewrite n; rewrite e.
simpl.
rewrite n.
intuition. (*case !f1,f2*)
apply not_true_is_false in n.
destruct (bool_dec (f2 a) true).
rewrite n;rewrite e.
simpl.
rewrite n.
intuition.
apply not_true_is_false in n0.
rewrite n;rewrite n0.
intuition.
Defined.

Lemma filter_combine: forall (xs : list nat) (f1 :nat -> bool) (f2 : nat -> bool),
filter f1 (filter f2 xs) = filter ( fun x: nat => (f1 x) && f2 x) xs.
Proof.
intros.
induction xs.
simpl.
reflexivity.
simpl.
destruct (bool_dec (f1 a) true); intros. (*case f1,f2*)
destruct (bool_dec (f2 a) true); intros.
rewrite e; rewrite e0.
simpl.
rewrite e.
rewrite IHxs.
intuition. (*case f1,!f2*)
apply not_true_is_false in n as e0.
rewrite e; rewrite e0.
simpl.
intuition. (*case !f1,f2*)
apply not_true_is_false in n as e.
destruct (bool_dec (f2 a) true); intros.
rewrite e; rewrite e0.
simpl.
rewrite e.
intuition. (*case !f1,!f2*)
apply not_true_is_false in n0 as e0.
rewrite e; rewrite e0.
intuition.
Defined.

  (*lemma f1 -> f2 then (filter f2 (filter f1 xs)) = filter f2 xs*)
  (*made specific for convienience*)
Lemma filter_nat_helper_right: forall (a : nat) (b :nat) (xs : list nat), (a>=b)-> 
  (filter (fun x0 : nat => negb(x0 <=? a))) (filter (fun x0 : nat => negb(x0 <=? b)) xs)=
(filter (fun y : nat => negb(y <=? a)) xs).
Proof.
intros.
induction xs. (*induction xs*)
simpl. (*base case*)
intuition.
simpl. (*step*)
destruct (le_gt_dec a0 b). (*case a0 <= b*)
apply leb_correct in l as l1.
rewrite l1; simpl.
apply (le_trans a0 b a) in l.
apply leb_correct in l.
rewrite l; simpl.
intuition.
intuition. 
apply leb_correct_conv in g. (*case a0 > b*)
rewrite g; simpl.
destruct (le_gt_dec a0 a).
apply leb_correct in l.
rewrite l; simpl.
intuition.
apply leb_correct_conv in g0.
rewrite g0; simpl.
rewrite IHxs.
intuition.
Defined.

Lemma filter_nat_helper_left: forall (xs : list nat) (a:nat) (b:nat),
  (b > a) -> (filter (fun y : nat => (y <=? a) && (y <=? b)) xs) = filter (fun y : nat => y <=? a) xs.
Proof.
intros.
induction xs.
simpl. (*base case*)
intuition.
simpl. (*step*)
destruct (le_lt_dec a0 a). (*case a0 <= a*)
apply (gt_le_trans b a a0) in H.
apply leb_correct in l.
rewrite l.
apply gt_leb_conv in H.
apply leb_correct in H.
rewrite H.
rewrite andb_true_l.
rewrite IHxs.
intuition.
intuition. (*case a < a0*)
apply leb_correct_conv in l.
rewrite l.
rewrite andb_false_l.
intuition.
Defined.

(*Vital lemma: convert list to recursion tree for quickSort*)
Lemma create_qs_tree: forall (l : list nat), (qs_tree l).
Proof.
intros.
induction l. (*induction l*)
constructor. (*base*)
constructor. (*step*)
induction IHl. (*induction on IH : qs_tree*)
constructor. (*base*)
simpl. (*step left side*)
destruct (le_lt_dec x a). (*case x in left branch*)
apply leb_correct in l.
rewrite l.
constructor. (*recurse*)
rewrite filter_commutative. (*left recursion branch*)
intuition.
rewrite filter_commutative. (*right recursion branch*)
intuition. 
apply leb_correct_conv in l as l2. (*if head xs not left*)
rewrite l2.
apply (filter_nat_helper_left xs a x) in l.
rewrite filter_combine in IHIHl1.
rewrite <- l.
intuition.
induction IHl. (*recurse right branch*)
simpl.
constructor.
simpl.
destruct (le_gt_dec x a). (*if head xs not in right branch*)
apply leb_correct in l as l0;
rewrite l0.
simpl.
intuition.
apply (filter_nat_helper_right a x xs) in l.
rewrite <- l.
intuition. (*if head xs in right branch*)
apply leb_correct_conv in g.
rewrite g.
simpl.
constructor. (*recurse*)
rewrite filter_commutative.
intuition.
rewrite filter_commutative.
intuition.
Defined.

(*Definition quickSort creates recursion tree for given list and hands it to qs_helper which executes it*)
Definition quickSort (ls :list nat) := qs_helper ls (create_qs_tree ls).

(*Test  quickSort*)

Definition l := 5 :: 3 :: 0 :: nil.
Eval compute in ((quickSort l)). 

(*Proof Correctness quickSort*)
  (*Note this prove uses that this holds for the recursion tree made by our definition xs*)
Lemma qs_contains : forall (xs : list nat) (x : nat), 
  (In x xs) -> (In x (quickSort xs)).
Proof.
intros.
unfold quickSort.
induction (create_qs_tree xs). (*induction on recursion tree*)
intuition. (*base*)
unfold In in H. (*step*)
simpl.
destruct H. (*split x = x0 or x in xs*)
rewrite <- H. (*case x = x0*)
simpl.
intuition. (*case x in xs*)
apply in_or_app. (*split x left or right after sorting*)
destruct (le_gt_dec x x0). 
(*case x <= x0*)
pose proof (filter_In (fun y => leb y  x0) x (xs)) as filter_In.
apply leb_correct in l0.
intuition.
(*case x > x0*)
pose proof (filter_In (fun y => negb (leb y  x0)) x (xs)) as filter_In.
apply leb_correct_conv in g.
apply negb_true_iff in g.
intuition.
Qed.

  (*Note this proof does not use that the recursion tree is made by our definition 
    (This is slightly more powerfull but harder to prove)*)
Lemma qs_maintains : forall (xs : list nat) (x : nat) (conc : qs_tree xs), 
  (In x (qs_helper xs conc))-> (In x xs).
Proof.
intros.
induction conc. (*induction on conc*)
intuition. (*base*)
simpl in H. (*step*)
apply in_app_or in H.
destruct H. (*case x is in the left side*)
intuition.
apply filter_In in H0.
intuition.
unfold In in H. (*case x is the pivot*)
destruct H.
unfold In.
intuition. (*case x is in the right side*)
intuition.
apply filter_In in H0.
intuition.
Qed.

Lemma qs_In_equiv : forall (xs : list nat) (x : nat), 
  (In x (quickSort xs)) <-> ( In x xs).
Proof.
intros.
intuition.
unfold quickSort in H. 
apply (qs_maintains xs x (create_qs_tree xs)).
intuition.
apply qs_contains.
intuition.
Qed.

(*Other easier to use definition of HdRel only one way conversion is needed*)
Lemma HdRel_redef : forall (xs : list nat) (a : nat) (f : nat-> nat -> Prop),
  (forall (x:nat), (In x xs) -> (f a x)) -> (HdRel f a xs).
Proof.
intros.
induction xs.
constructor.
constructor.
apply H.
intuition.
Qed. 

(*if we have two sorted arrays xls,xrs 
  and every element in xls is smaller then every element in xrs then xls++xrs is sorted*)
Lemma sorted_comb : forall (xls: list nat) (xrs: list nat),
  (Sorted le xls) -> (Sorted le xrs) -> 
  (forall (x:nat), (In x xls) -> (HdRel le x xrs)) ->
      Sorted le (xls ++ xrs).
Proof.
intros.
induction xls. (*induction on xls*)
simpl. (*base*)
intuition.
simpl. (*step*)
constructor. (*prove sorted properties*)
apply Sorted_inv in H. (*tail is sorted / holds by IH*)
intuition.
apply Sorted_inv in H. (*head is smaller then all elements in tail*)
intuition.
destruct xls. (*case xrs is empty*)
destruct xrs. (*case xls is also empty*)
simpl.
constructor. (*HdRel holds by definition*)
simpl. (*get head of nill++xls*)
apply H1.
constructor.
intuition. (*get head of xrs*)
constructor.
apply HdRel_inv in H3.
intuition.
Qed.

(*final goal proof that quickSort sorts a list*)
Lemma qs_sorted : forall (xs: list nat),
  Sorted le (quickSort xs).
Proof. 
intros.
unfold quickSort. (*unfold quickSort*)
induction (create_qs_tree (xs)). (*induction on recursion tree*)
simpl. (*step recursion tree is empty (then by def xs is empty*)
intuition. (*node recursion tree*)
simpl. (*to prove left recursion results appended by right recursion result is sorted*)
apply sorted_comb. (*IH left is sorted*) 
intuition. (*to prove pivot appended right recursion is sorted*) 
constructor.
intuition. (*IH right is sorted*)
apply HdRel_redef. (*to prove x is smaller then everything in the right branch*)
intros.
apply qs_maintains in H. (*use In x xs <-> In x quickSort xs*)
apply filter_In in H. (*effect of filter*) 
intuition.
apply negb_true_iff in H1.
apply leb_complete_conv in H1.
intuition. 
intuition. (*to prove everything in the right branch is smaller then everything in pivot + left*)
apply HdRel_redef.
intuition.
apply qs_maintains in H. (*use In x xs <-> In x quickSort xs*)
apply filter_In in H. (*effect of filter*)
apply in_inv in H0. (*trivial clean up basic algebra differences*) 
intuition.
apply leb_complete in H2.
rewrite <- H.
intuition.
apply qs_maintains in H.
apply filter_In in H.
intuition.
apply negb_true_iff in H3.
apply leb_complete in H2.
apply leb_complete_conv in H3.
intuition.
Qed.