Module Logic.
  Lemma and_proj : forall {A B : Prop}, A /\ B -> A.
    intros A B H.
    destruct H as [H_A H_B].
    exact H_A.
  Qed.

  Lemma and_commut : forall {A B : Prop}, A /\ B -> B /\ A.
    intros A B H.
    destruct H as [H_A H_B].
    split.
    - exact H_B.
    - exact H_A.
  Qed.

  Lemma negneg : forall {A : Prop}, A -> ~ ~ A.
    intros A H.
    unfold not.
    intro nH.
    apply nH.
    exact H.
  Qed.

  Lemma negneg_auto : forall {A : Prop}, A -> ~ ~ A.
    tauto.
  Qed.
 
 Lemma negneg_rev : forall {A : Prop}, ~ ~ A -> A.
   unfold not.
   intros A nnH.
 Abort.
End Logic.

Module Peano.
  Inductive N : Set :=
  | O
  | S (n : N).

  Fixpoint plus (n m : N) : N :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Lemma plus_0_m : forall m, plus O m = m.
    intro m.
    simpl.
    reflexivity.
  Qed.

  Lemma plus_n_0 : forall n, plus n O = n.
    intro n.
    induction n.
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHn.
      reflexivity.
  Qed.
End Peano.

Module Even.
  Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n, even n -> even (S (S n)).

  Definition odd (n : nat) : Prop :=
    even (S n).

  Lemma even_or_odd : forall (n : nat), even n \/ odd n.
    intro n.
    induction n.
    - left.
      apply even_O.
    - destruct IHn.
      + right.
        unfold odd.
        apply even_S.
        exact H.
      + left.
        unfold odd in H.
        exact H.
  Qed.
End Even.

Module Factorial.
  Require Import Coq.Arith.Factorial.

  Check fact.
  Check lt_O_fact.

  Definition safe_fact (n : nat) : {n : nat | 0 < n}.
    exists (fact n).
    apply lt_O_fact.
  Defined.
End Factorial.
