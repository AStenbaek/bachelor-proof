From Coq Require Import Lists.List.

(* Replace an element in a list with another *)
Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil => nil
  | h :: t =>
    match n with
    | O => x :: t
    | S n' => h :: replace n' x t
    end
  end.

(* Replacing in an empty list is also an empty list *)
Lemma replace_nil : forall A n (x:A),
    replace n x nil = nil.
Proof.
  intros.
  destruct n; auto.
Qed.

(* Replacing an element does not change the list length *)
Lemma length_replace : forall A n x (l:list A),
    length (replace n x l) = length l.
Proof with auto.
  intros.
  generalize dependent n.
  induction l; intros n.
  - destruct n...
  - destruct n...
    simpl.
    rewrite IHl...
Qed.

(* Replace actually replaces the expected element in the list *)
Lemma lookup_replace_eq : forall A n x (l:list A),
    n < length l ->
    nth_error (replace n x l) n = Some x.
Proof.
  intros.
  generalize dependent n.
  induction l.
  - intros.
    simpl in H.
    apply PeanoNat.Nat.nlt_0_r in H.
    destruct H.
  - intros.
    destruct n.
    + reflexivity.
    + simpl.
      apply IHl.
      simpl in H.
      rewrite PeanoNat.Nat.succ_lt_mono.
      apply H.
Qed.

(* Replace does not change the list other than the element at the changed index *)
Lemma lookup_replace_neq : forall A n m x (l:list A),
    n <> m ->
    nth_error (replace n x l) m = nth_error l m.
Proof with auto.
  intros A n.
  induction n.
  - intros.
    destruct l...
    simpl.
    destruct m...
    destruct H...
  - intros.
    simpl.
    destruct l...
    destruct m...
    simpl.
    apply IHn.
    rewrite PeanoNat.Nat.succ_inj_wd_neg in H...
Qed.
