From BSC Require Export Lang.
Export Lang.

Definition heap_typing (Σ : store_ty) (σ : store) : Prop :=
  length Σ = length σ /\
  (forall l, l < length σ ->
             has_type Σ empty (store_lookup σ l) (store_ty_lookup Σ l)).

Reserved Notation "Σ '⊆' Σ'" (at level 40).
Inductive extends : store_ty -> store_ty -> Prop :=
| extends_nil : forall Σ', nil ⊆ Σ'
| extends_cons : forall Σ Σ' T, Σ ⊆ Σ' -> (T::Σ) ⊆ (T::Σ')
where "Σ '⊆' Σ'" := (extends Σ Σ').


Lemma extends_lookup : forall l Σ Σ',
    l < length Σ ->
    Σ ⊆ Σ' ->
    store_ty_lookup Σ l = store_ty_lookup Σ' l.
Proof.
  intros l Σ.
  generalize dependent l.
  induction Σ.
  - intros.
    inversion H.
  - intros.
    destruct Σ'.
    + inversion H0.
    + inversion H0; subst.
      destruct l.
      * unfold store_ty_lookup; auto.
      * simpl in H.
        rewrite <- Nat.succ_lt_mono in H.
        eapply IHΣ in H; eauto.
Qed.

Lemma length_extends : forall l Σ Σ',
    l < length Σ ->
    Σ ⊆ Σ' ->
    l < length Σ'.
Proof.
  intros.
  generalize dependent l.
  induction H0; intros.
  - inversion H.
  - simpl.
    destruct Σ'.
    + inversion H0; subst; auto.
    + simpl.
      destruct l.
      * apply Nat.lt_0_succ.
      * simpl in H.
        rewrite <- Nat.succ_lt_mono in H.
        apply IHextends in H.
        rewrite <- Nat.succ_lt_mono.
        auto.
Qed.

Lemma extends_app : forall Σ Σ',
    Σ ⊆ (Σ ++ Σ').
Proof.
  induction Σ.
  - intros.
    simpl.
    constructor.
  - intros.
    simpl.
    apply extends_cons.
    apply IHΣ.
Qed.

Lemma extends_refl : forall Σ, Σ ⊆ Σ.
Proof.
  induction Σ; constructor; auto.
Qed.

Lemma store_lookup_shift : forall Σ l n m,
    l < length Σ ->
    tshift n m (store_ty_lookup Σ l) = store_ty_lookup (map (tshift n m) Σ) l.
Proof.
  induction Σ.
  - intros.
    inversion H.
  - intros.
    simpl.
    destruct l.
    + unfold store_ty_lookup.
      auto.
    + unfold store_ty_lookup.
      simpl.
      simpl in H.
      rewrite <- Nat.succ_lt_mono in H.
      eapply IHΣ in H.
      unfold store_ty_lookup in H.
      apply H.
Qed.

Lemma store_lookup_subst : forall Σ l n T,
    l < length Σ ->
    tsubst n T (store_ty_lookup Σ l) = store_ty_lookup (map (tsubst n T) Σ) l.
Proof.
  induction Σ.
  - intros.
    inversion H.
  - intros.
    simpl.
    destruct l.
    + unfold store_ty_lookup; auto.
    + unfold store_ty_lookup; simpl.
      simpl in H.
      rewrite <- Nat.succ_lt_mono in H.
      eapply IHΣ in H.
      unfold store_ty_lookup in H.
      apply H.
Qed.


Lemma store_extends_tshift : forall Σ Σ' n m,
    Σ ⊆ Σ' -> (map (tshift n m) Σ) ⊆ (map (tshift n m) Σ').
Proof.
  intros.
  induction H.
  - simpl.
    constructor.
  - simpl.
    constructor.
    apply IHextends.
Qed.

Lemma store_weakening : forall Σ Σ' Γ e T,
    Σ ⊆ Σ' ->
    has_type Σ Γ e T ->
    has_type Σ' Γ e T.
Proof.
  intros.
  generalize dependent Σ'.
  induction H0; intros; eauto using store_extends_tshift.
  rewrite extends_lookup with (Σ' := Σ'); eauto.
  apply T_Loc.
  eapply length_extends; eauto.
Qed.

Lemma extends_shift : forall Σ Σ',
    Σ ⊆ Σ' -> (map (tshift 1 0) Σ) ⊆ (map (tshift 1 0) Σ').
Proof.
  induction Σ.
  - intros.
    simpl.
    constructor.
  - intros.
    simpl.
    inversion H.
    subst.
    simpl.
    constructor.
    apply IHΣ.
    apply H3.
Qed.
