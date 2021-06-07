Set Warnings "-notation-overridden,-parsing".

From BSC Require Import SubShift.

Import SubShift.

Lemma canonical_forms_fun : forall Σ e T1 T2,
    has_type Σ empty e <{{ T1 -> T2 }}> ->
    value e ->
    exists e', e = <{λ , e'}>.
Proof.
  intros.
  destruct H0;
    inversion H; subst.
  exists e; eauto.
Qed.

Lemma canonical_forms_bool : forall Σ e,
    has_type Σ empty e <{{ Bool }}> ->
    value e ->
    e = e_true \/ e = e_false.
Proof.
  intros.
  destruct H0; inversion H; subst.
  - left; auto.
  - right; auto.
Qed.

Theorem progress : forall Σ σ e T,
    has_type Σ empty e T ->
    heap_typing Σ σ ->
    value e \/ exists e' σ', (σ, e) --> (σ', e').
Proof.
  intros.
  remember empty as G.
  induction H.
  (* T_Var *)
  - rewrite HeqG in H.
    destruct k; discriminate.
  (* T_App *)
  - right.
    destruct IHhas_type1; eauto.
    + destruct IHhas_type2; eauto.
      * rewrite HeqG in H.
        apply canonical_forms_fun in H; auto.
        destruct H as [e'' H'].
        subst.
        do 2 eexists.
        apply ST_AppRec.
        apply H3.
      * destruct H3.
        destruct H3.
        exists <{ e1 x }>.
        eexists.
        constructor; eauto.
    + do 2 destruct H2.
      exists <{ x e2 }>.
      eexists.
      constructor; eauto.
  (* T_Rec *)
  - left; constructor.
  (* T_Unit *)
  - left; constructor.
  (* T_True *)
  - left; constructor.
  (* T_False *)
  - left; constructor.
  (* T_If *)
  - right.
    destruct IHhas_type1; auto.
    + rewrite HeqG in H.
      apply canonical_forms_bool in H; auto.
      destruct H; [
        subst; exists e2; eexists; constructor |
        subst; exists e3; eexists; constructor].
    + do 2 destruct H3.
      exists <{ if x then e2 else e3 }>.
      eexists.
      constructor; eauto.
  (* T_Int *)
  - left; constructor.
  (* T_Binop *)
  - destruct IHhas_type1; auto.
    + destruct IHhas_type2; auto.
      * right;
        destruct bop0;
        simpl in H;
        inversion H; subst;
        inversion H3; subst; inversion H1; subst;
          inversion H4; subst; inversion H2; subst;
            do 2 eexists; try (apply ST_Binop3).
      * do 2 destruct H4.
        right.
        exists (e_binop bop0 e1 x).
        eexists.
        apply ST_Binop2; eauto.
    + do 2 destruct H3.
      right.
      exists (e_binop bop0 x e2).
      eexists.
      apply ST_Binop1; eauto.
  (* T_Pair *)
  - destruct IHhas_type1; auto.
    + destruct IHhas_type2; auto.
      do 2 destruct H3.
      right.
      exists <{ (e1, x) }>.
      eexists.
      constructor; eauto.
    + right.
      do 2 destruct H2.
      exists <{ (x, e2) }>.
      eexists.
      constructor; eauto.
  (* T_Fst *)
  - destruct IHhas_type; eauto.
    + right.
      inversion H; subst; inversion H1.
      exists e1.
      eexists.
      constructor; auto.
    + right.
      do 2 destruct H1.
      exists (e_fst x).
      eexists.
      constructor; eauto.
  (* T_Snd *)
  - destruct IHhas_type; auto.
    + right.
      inversion H; subst; inversion H1.
      exists e2.
      eexists.
      constructor; eauto.
    + right.
      do 2 destruct H1.
      exists (e_snd x).
      eexists.
      constructor; eauto.
  (* T_Inl *)
  - destruct IHhas_type; auto.
    + do 2 destruct H1.
      right.
      exists <{ inl x }>.
      eexists.
      constructor; eauto.
  (* T_Inr *)
  - destruct IHhas_type; auto.
    + do 2 destruct H1.
      right.
      exists <{ inr x }>.
      eexists.
      constructor; eauto.
  (* T_Case *)
  - destruct IHhas_type1; eauto.
    + right.
      inversion H; subst; inversion H3; subst.
      * do 2 eexists.
        apply ST_CaseInl; auto.
      * do 2 eexists.
        apply ST_CaseInr; auto.
    + do 2 destruct H3.
      right.
      do 2 eexists.
      apply ST_Case.
      apply H3.
  (* T_TAbs *)
  - left.
    constructor.
  (* T_TApp *)
  - apply IHhas_type in HeqG.
    destruct HeqG.
    + inversion H; subst; inversion H1.
      right.
      do 2 eexists.
      eapply ST_TAppAbs.
    + destruct H1 as [e'].
      destruct H1.
      right.
      do 2 eexists.
      eapply ST_TApp.
      apply H1.
    + apply H0.
  (* T_Pack *)
  - apply IHhas_type in HeqG.
    destruct HeqG.
    + left; auto.
    + right.
      do 2 destruct H1.
      do 2 eexists.
      econstructor.
      apply H1.
    + auto.
  (* T_Unpack *)
  - apply IHhas_type1 in HeqG.
    destruct HeqG.
    + inversion H; subst; inversion H2.
      right.
      do 2 eexists.
      eapply ST_UnpackPack.
      apply H4.
    + destruct H2 as [e1'].
      destruct H2.
      right.
      do 2 eexists.
      econstructor.
      apply H2.
    + auto.
  (* T_Fold *)
  - apply IHhas_type in HeqG.
    destruct HeqG.
    + left.
      constructor.
      apply H1.
    + right.
      destruct H1 as [e'].
      destruct H1.
      exists <{ fold e' }>.
      eexists.
      constructor.
      apply H1.
    + auto.
  (* T_Unfold *)
  - apply IHhas_type in HeqG.
    destruct HeqG.
    + inversion H; subst; inversion H1.
      right.
      exists e0.
      eexists.
      constructor.
      apply H3.
    + destruct H1 as [e'].
      destruct H1.
      right.
      exists <{ unfold e' }>.
      eexists.
      constructor; eauto.
    + auto.
  (* T_Loc *)
  - left; auto.
  (* T_Alloc *)
  - apply IHhas_type in HeqG; auto.
    destruct HeqG.
    + right.
      do 2 eexists.
      apply ST_AllocValue; auto.
    + right.
      do 2 destruct H1.
      do 2 eexists.
      constructor; eauto.
  (* T_Assign *)
  - destruct IHhas_type1; destruct IHhas_type2; auto.
    + right.
      inversion H; subst; inversion H2; subst.
      do 2 eexists.
      apply ST_AssignValue; auto.
      inversion H0; subst.
      rewrite H4 in H7; auto.
    + right.
      do 2 destruct H3; do 2 eexists.
      apply ST_Assign2; eauto.
    + right.
      do 2 destruct H2; do 2 eexists;
        apply ST_Assign1; eauto.
    + right.
      do 2 destruct H2; do 2 eexists;
        apply ST_Assign1; eauto.
  (* T_Load *)
  - apply IHhas_type in HeqG; auto.
    destruct HeqG.
    + inversion H; subst; inversion H1; subst.
      right.
      do 2 eexists.
      apply ST_LoadLoc.
      inversion H0.
      rewrite H2 in H5; auto.
    + right; do 2 destruct H1; do 2 eexists.
      apply ST_Load.
      eauto.
Qed.

      
Theorem preservation : forall Σ σ σ' e e' T,
    has_type Σ empty e T ->
    heap_typing Σ σ ->
    (σ, e) --> (σ', e') ->
    exists Σ',
      Σ ⊆ Σ' /\
      has_type Σ' empty e' T /\
      heap_typing Σ' σ'.
Proof.
  intros Σ σ σ' e e' T H Hheap H'.
  generalize dependent e'.
  remember empty as G.
  induction H; intros; subst.
  (* T_Var *)
  - inversion H'.
  (* T_App *)
  - inversion H'; eauto; subst.
    assert (empty = empty ++ empty) by auto.
    + exists Σ.
      split.
      apply extends_refl.
      split; eauto.
      assert (empty = empty ++ empty) by auto.
      rewrite H1.
      apply subst_preservation with <{{ T2 }}>; eauto.
      apply subst_preservation with <{{ T2 -> T1 }}>.
      * inversion H; eauto.
      * rewrite H1 in H.
        apply shift_preservation with (Δ:=(T2::empty)) in H.
        simpl in H.
        simpl.
        apply H.
    + edestruct IHhas_type1; eauto.
      destruct H1.
      destruct H3.
      eexists.
      split; eauto.
      split; eauto.
      econstructor; eauto.
      eapply store_weakening; eauto.
    + edestruct IHhas_type2; eauto.
      destruct H1.
      destruct H2.
      eexists.
      split; eauto.
      split; eauto.
      econstructor; eauto.
      eapply store_weakening; eauto.
  (* T_Rec *)
  - inversion H'; eauto.
  (* T_Unit *)
  - inversion H'; eauto.
  (* T_True *)
  - inversion H'.
  (* T_False *)
  - inversion H'.
  (* T_If *)
  - inversion H'; subst; eauto.
    + edestruct IHhas_type1; eauto.
      destruct H2.
      destruct H4.
      eexists.
      split; eauto.
      split; eauto.
      econstructor; eauto.
      eapply store_weakening; eauto.
      eapply store_weakening; eauto.
    + exists Σ.
      split; [ apply extends_refl
             | split; [ apply H0
                      | apply Hheap ] ].
    + exists Σ.
      split; [ apply extends_refl
             | split; [ apply H1
                      | apply Hheap ] ].
  (* T_Int *)
  - inversion H'.
  (* T_Binop *)
  - inversion H'; subst; eauto.
    + edestruct IHhas_type1; eauto.
      destruct H2.
      destruct H4.
      eexists.
      split; eauto.
      split; eauto.
      econstructor; eauto.
      eapply store_weakening; eauto.
    + edestruct IHhas_type2; eauto.
      destruct H2.
      destruct H3.
      eexists.
      split; eauto.
      split; eauto.
      econstructor; eauto.
      eapply store_weakening; eauto.
    + exists Σ.
      split; [ apply extends_refl
             | split; [ destruct bop0; inversion H; subst; simpl; eauto
                      | apply Hheap ] ].
      * destruct (Z.ltb v1 v2); eauto.
      * destruct (Z.eqb v1 v2); eauto.
  (* T_Pair*)
  - inversion H'; subst; eauto.
    + edestruct IHhas_type1; eauto.
      destruct H1.
      destruct H3.
      eexists.
      split; eauto.
      split; eauto.
      econstructor; eauto.
      eapply store_weakening; eauto.
    + edestruct IHhas_type2; eauto.
      destruct H1.
      destruct H2.
      eexists.
      split; eauto.
      split; eauto.
      econstructor; eauto.
      eapply store_weakening; eauto.
  (* T_Fst *)
  - inversion H'; subst; eauto.
    + edestruct IHhas_type; eauto.
      destruct H0.
      destruct H2.
      eexists.
      split; eauto.
    + inversion H; subst.
      eexists;
        split; [ apply extends_refl
               | split; auto ].
  (* T_Snd *)
  - inversion H'; subst; eauto.
    + edestruct IHhas_type; eauto.
      destruct H0.
      destruct H2.
      eexists.
      split; eauto.
    + inversion H; subst.
      eexists;
        split; [ apply extends_refl
               | split; auto ].
  (* T_Inl *)
  - inversion H'; eauto; subst.
    edestruct IHhas_type; eauto.
    destruct H0.
    destruct H2.
    exists x.
    split; [ auto | split; auto ].
  (* T_Inr *)
  - inversion H'; eauto; subst.
    edestruct IHhas_type; eauto.
    destruct H0.
    destruct H2.
    exists x.
    split; [ auto | split; auto ].
  (* T_Case *)
  - inversion H'; subst; eauto.
    + edestruct IHhas_type1; eauto.
      destruct H2.
      destruct H4.
      exists x.
      split; auto.
      split; auto.
      econstructor; eauto; eapply store_weakening; eauto.
    + inversion H; subst.
      assert (empty = empty ++ empty) by auto.
      rewrite H2.
      eexists.
      split; [ apply extends_refl
             | split; [ | eauto ] ].
      apply subst_preservation with T1; simpl; eauto.
    + inversion H; subst.
      assert (empty = empty ++ empty) by auto.
      rewrite H2.
      eexists.
      split; [ apply extends_refl
             | split; [ | eauto ] ].
      apply subst_preservation with T2; simpl; eauto.
  (* T_TAbs *)
  - inversion H'.
  (* T_TApp *)
  - inversion H'; subst.
    + edestruct IHhas_type; eauto.
      destruct H0.
      destruct H2.
      eexists.
      eauto.
    + inversion H; subst.
      eexists.
      split.
      apply extends_refl.
      split; auto.
      assert (Σ = map (tsubst 0 T2) (map (tshift 1 0) Σ)).
      { symmetry.
        apply tsubst_tshift_gamma. }
      rewrite H0.
      assert (empty = map (tsubst 0 T2) (map (tshift 1 0) empty)) by auto.
      rewrite H1.
      eapply tsubst_preservation.
      apply H3.
  (* T_Pakc *)
  - inversion H'; subst.
    edestruct IHhas_type; eauto.
    destruct H0.
    destruct H2.
    eexists; eauto.
  (* T_Unpack *)
  - inversion H'; subst.
    + edestruct IHhas_type1; eauto.
      destruct H1.
      destruct H3.
      eexists.
      split; eauto.
      split; eauto.
      econstructor; eauto.
      apply store_weakening with (Σ := (map (tshift 1 0) Σ)).
      * apply extends_shift.
        apply H1.
      * apply H0.
    + inversion H; subst.
      assert (empty = empty ++ empty) by auto.
      rewrite H1.
      apply tsubst_preservation with (n := 0) (T' := T0) in H0.
      rewrite tsubst_tshift in H0.
      simpl in H0.
      rewrite tsubst_tshift_gamma in H0.
      exists Σ.
      split; [ apply extends_refl
             | split; [ | apply Hheap ] ].
      eapply subst_preservation; eauto.
      simpl.
      auto.
  (* T_Fold *)
  - inversion H'; subst.
    specialize IHhas_type with (e' := e'0).
    destruct IHhas_type; eauto.
    destruct H0.
    destruct H2.
    eauto.
  (* T_Unfold *)
  - inversion H'; subst.
    + exists Σ.
      split; [ apply extends_refl
             | split; [ | apply Hheap ] ].
      inversion H1; subst; inversion H; subst; auto.
    + edestruct IHhas_type; eauto.
      destruct H0.
      destruct H2.
      exists x.
      eauto.
  (* T_Loc *)
  - inversion H'.
  (* T_Alloc *)
  - inversion H'; subst.
    + edestruct IHhas_type; eauto.
      destruct H0.
      destruct H2.
      exists x; eauto.
    + exists (Σ ++ T :: nil).
      split.
      * apply extends_app.
      * split.
        { assert (T = store_ty_lookup (Σ ++ T :: nil) (length Σ)).
          { unfold store_ty_lookup.
            erewrite nth_error_app2.
            rewrite Nat.sub_diag.
            simpl.
            reflexivity.
            auto. }
          assert (Ty_Ref T = Ty_Ref (store_ty_lookup (Σ ++ T :: nil) (length Σ)))
            by (rewrite <- H0; auto).
          rewrite H2.
          inversion Hheap.
          rewrite H3.
          eapply T_Loc.
          rewrite app_length.
          simpl.
          rewrite Nat.add_comm.
          simpl.
          rewrite H3.
          auto. }
        inversion Hheap.
        constructor.
        do 2 rewrite app_length.
        simpl.
        rewrite H0.
        auto.
        intros.
        rewrite app_length in H3.
        rewrite Nat.add_comm in H3.
        simpl in H3.
        rewrite Nat.lt_succ_r in H3.
        destruct H3.
        { rewrite <- H0.
          unfold store_ty_lookup.
          rewrite nth_error_app2; auto.
          rewrite Nat.sub_diag.
          simpl.
          inversion Hheap.
          rewrite H3.
          unfold store_lookup.
          rewrite nth_error_app2; auto.
          rewrite Nat.sub_diag.
          simpl.
          eapply store_weakening; eauto.
          apply extends_app. }
        specialize H2 with (l := l).
        rewrite <- Nat.lt_succ_r in H3.
        apply H2 in H3 as H4.
        unfold store_ty_lookup.
        rewrite nth_error_app1; [ | rewrite <- H0 in H3; auto ].
        inversion Hheap.
        rewrite H5 in H0.
        unfold store_lookup.
        rewrite nth_error_app1; [ | rewrite <- H0 in H3; auto ].
        eapply store_weakening; eauto.
        apply extends_app.
  (* T_Assign *)
  - inversion H'; subst.
    + edestruct IHhas_type1; eauto.
      destruct H1 as [ A [ B C ] ].
      exists x.
      split; auto.
      split; auto.
      econstructor; eauto.
      eapply store_weakening; eauto.
    + edestruct IHhas_type2; eauto.
      destruct H1 as [ A [ B C ] ].
      exists x.
      split; auto.
      split; auto.
      apply T_Assign with (T := T); eauto.
      eapply store_weakening; eauto.
    + exists Σ.
      split; [ apply extends_refl
             | split; [ constructor | ] ].
      constructor.
      * inversion Hheap.
        rewrite length_replace.
        apply H1.
      * intros.
        destruct Nat.eq_decidable with (n := l) (m := l0).
        { symmetry in H2.
          subst.
          inversion H; subst.
          unfold store_lookup.
          rewrite lookup_replace_eq.
          apply H0.
          apply H7. }
        { unfold store_lookup.
          rewrite lookup_replace_neq; auto.
          inversion Hheap.
          rewrite length_replace in H1.
          apply H5 in H1.
          apply H1. }
  (* T_Load *)
  - inversion H'; subst.
    + edestruct IHhas_type; eauto.
      destruct H0 as [ A [ B C ] ].
      eauto.
    + exists Σ.
      split; [ apply extends_refl | ].
      split; auto.
      inversion H; subst.
      inversion Hheap.
      apply H2 in H1.
      apply H1.
Qed.
