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

Module Natural.
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
End Natural.
