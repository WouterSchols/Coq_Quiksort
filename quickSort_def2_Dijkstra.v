Require Import Coq.Lists.List.
Require Import Coq.Structures.OrdersFacts.
Require Import Omega.

Inductive qs_tree : list nat -> Type :=
| qs_tree_base : qs_tree nil
| qs_tree_step : forall ( x: nat) (xs: list nat), 
  qs_tree (filter (fun y => leb y  x) (xs)) -> 
  qs_tree (filter (fun y => negb (leb y x)) (xs)) -> 
    qs_tree (cons x xs).

(*new definition of quicksort using invariant*)

Lemma qs_acc_inv_1_0'' : forall (l:list nat)(x: nat)(xs : list nat),
qs_tree l -> l = cons x xs -> qs_tree (filter (fun y => leb y  x) xs).
intros l x xs H.
inversion H.
congruence.
intro H3.
inversion H3.
rewrite H5 in H0.
rewrite H6 in H0.
exact H0.
Defined.

Lemma qs_acc_inv_1_1'' : forall (l:list nat)(x: nat)(xs : list nat),
qs_tree l -> l = cons x xs -> qs_tree (filter (fun y => negb (leb y x)) xs).
intros l x xs H.
inversion H.
congruence.
intro H3.
inversion H3.
rewrite H5 in H1.
rewrite H6 in H1.
exact H1.
Defined.

Fixpoint qss (xl : list nat) (conc : qs_tree xl) {struct conc}:= 
match xl as _y0 return (xl = _y0) -> list nat with 
   | nil       => fun  _h0 => nil
   | cons x xs => fun _h0 => 
      (qss (filter (fun y => leb y  x) xs)(qs_acc_inv_1_0'' _ _ _ conc _h0))
      ++ (cons x (qss (filter (fun y => negb (leb y x)) xs)(qs_acc_inv_1_1'' _ _ _ conc _h0)))
  end (refl_equal xl).










