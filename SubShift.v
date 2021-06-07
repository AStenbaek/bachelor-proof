Set Warnings "-notation-overridden,-parsing".

From BSC Require Import StoreProp.
Export StoreProp.

(* Sanity Check: Shifting by 0 should yield the same expression *)
Lemma shift_0 : forall (c : id) (e : expr),
    shift 0 c e = e.
Proof.
  intros c e.
  generalize dependent c.
  induction e;
    intros;
    simpl;
    try (rewrite IHe);
    try (rewrite IHe1; rewrite IHe2);
    try (rewrite IHe3);
    auto.
  destruct (i <? c).
  - reflexivity.
  - rewrite Nat.add_0_r.
    reflexivity.
Qed.

Lemma tshift_tshift : forall T n m,
    tshift 1 n (tshift 1 (n + m) T) = tshift 1 (S (n + m)) (tshift 1 n T).
Proof.
  induction T; intros; auto;
    try (simpl;
    specialize IHT with (n := S n);
    simpl in IHT;
    rewrite IHT;
    reflexivity);
    try (simpl;
         rewrite IHT1;
         rewrite IHT2;
         auto).
  (* Ty_Var *)
  - simpl.
    remember (i <? n + m) as b.
    remember (i <? n) as b'.
    destruct b; destruct b'; simpl.
    + rewrite <- Heqb'.
      symmetry in Heqb.
      rewrite Nat.ltb_lt in Heqb.
      apply Nat.lt_lt_succ_r in Heqb.
      rewrite <- Nat.ltb_lt in Heqb.
      rewrite Heqb.
      reflexivity.
    + rewrite <- Heqb'.
      symmetry in Heqb.
      rewrite Nat.ltb_lt in Heqb.
      rewrite Nat.succ_lt_mono in Heqb.
      rewrite <- Nat.ltb_lt in Heqb.
      rewrite Nat.add_comm with i 1.
      simpl.
      rewrite Heqb.
      reflexivity.
    + symmetry in Heqb.
      symmetry in Heqb'.
      rewrite Nat.ltb_nlt in Heqb.
      rewrite Nat.ltb_lt in Heqb'.
      apply Nat.lt_lt_add_r with (p:=m) in Heqb'.
      apply Heqb in Heqb'.
      destruct Heqb'.
    + symmetry in Heqb.
      symmetry in Heqb'.
      rewrite Nat.ltb_ge in Heqb.
      rewrite Nat.ltb_ge in Heqb'.
      rewrite Nat.succ_le_mono in Heqb.
      apply Nat.le_le_succ_r in Heqb'.
      rewrite <- Nat.ltb_ge in Heqb.
      rewrite <- Nat.ltb_ge in Heqb'.
      rewrite Nat.add_comm with i 1.
      simpl.
      rewrite Heqb.
      rewrite Heqb'.
      reflexivity.
  (* Ty_Ref *)
  - simpl.
    rewrite IHT.
    auto.
Qed.

Corollary tshift_tshift_0 : forall T n,
    tshift 1 0 (tshift 1 n T) = tshift 1 (S n) (tshift 1 0 T).
Proof.
  intros.
  assert (n = 0 + n) by auto.
  rewrite H.
  rewrite tshift_tshift.
  auto.
Qed.

Lemma tsubst_tshift : forall n T1 T2,
    tsubst n T1 (tshift 1 n T2) = T2.
Proof.
  intros.
  generalize dependent n.
  generalize dependent T1.
  induction T2; intros; auto;
    try (simpl;
         try (rewrite IHT2_1;
              rewrite IHT2_2);
         try (rewrite IHT2);
         auto).
  simpl.
  remember (i <? n) as a.
  symmetry in Heqa.
  destruct a.
  - simpl.
    rewrite Heqa.
    assert (i <> n)
      by (rewrite Nat.ltb_lt in Heqa;
          apply Nat.lt_neq in Heqa;
          auto).
    rewrite <- Nat.eqb_neq in H.
    rewrite H.
    reflexivity.
  - simpl.
    assert (~(i + 1 < n)).
    { rewrite Nat.add_comm.
      simpl.
      unfold not.
      intros.
      rewrite Nat.ltb_ge in Heqa.
      apply Nat.le_le_succ_r in Heqa.
      rewrite <- Nat.nle_gt in H.
      apply H in Heqa.
      destruct Heqa. }
    rewrite <- Nat.ltb_nlt in H.
    rewrite H.
    assert (i + 1 <> n).
    { unfold not.
      intros.
      rewrite Nat.ltb_ge in Heqa.
      rewrite <- H0 in Heqa.
      rewrite Nat.add_comm in Heqa.
      simpl in Heqa.
      apply Nat.nle_succ_diag_l in Heqa.
      apply Heqa. }
    rewrite <- Nat.eqb_neq in H0.
    rewrite H0.
    rewrite Nat.add_sub.
    reflexivity.
Qed.

Corollary tsubst_tshift_gamma : forall Γ n T,
    map (tsubst n T) (map (tshift 1 n) Γ) = Γ.
Proof.
  induction Γ.
  - intros.
    auto.
  - intros.
    simpl.
    rewrite IHΓ.
    rewrite tsubst_tshift.
    reflexivity.
Qed.


Lemma tshift_tsubst : forall T1 T2 n m,
    tshift 1 (n + m) (tsubst n T2 T1)
    =
    tsubst n (tshift 1 (n + m) T2) (tshift 1 (S (n + m)) T1).
Proof.
  intros T1.
  induction T1;
    intros;
    auto;
    try (simpl;
         specialize IHT1 with (n := S n);
         simpl in IHT1;
         rewrite IHT1;
         rewrite tshift_tshift_0;
         reflexivity);
    try (simpl;
         rewrite IHT1_1;
         rewrite IHT1_2;
         auto).
  (* Ty_Var *)
  - simpl.
    remember (i =? n) as b.
    remember (i <? S (n + m)) as b'.
    destruct b; destruct b'.
    + simpl.
      rewrite <- Heqb.
      reflexivity.
    + simpl.
      symmetry in Heqb.
      rewrite Nat.eqb_eq in Heqb.
      symmetry in Heqb'.
      rewrite Nat.ltb_nlt in Heqb'.
      assert (i <= n + m).
      { rewrite Heqb.
        apply Nat.le_add_r. }
      rewrite <- Nat.lt_succ_r in H.
      apply Heqb' in H.
      destruct H.
    + simpl.
      rewrite <- Heqb.
      remember (i <? n) as b''.
      destruct b''.
      * simpl.
        symmetry in Heqb''.
        rewrite Nat.ltb_lt in Heqb''.
        apply Nat.lt_lt_add_r with (p := m) in Heqb''.
        rewrite <- Nat.ltb_lt in Heqb''.
        rewrite Heqb''.
        reflexivity.
      * simpl.
        symmetry in Heqb'.
        rewrite Nat.ltb_lt in Heqb'.
        destruct i.
        ** simpl.
           symmetry in Heqb.
           rewrite Nat.eqb_neq in Heqb.
           symmetry in Heqb''.
           rewrite Nat.ltb_ge in Heqb''.
           inversion Heqb''.
           symmetry in H.
           apply Heqb in H.
           destruct H.
        ** simpl.
           rewrite Nat.sub_0_r.
           rewrite <- Nat.succ_lt_mono in Heqb'.
           rewrite <- Nat.ltb_lt in Heqb'.
           rewrite Heqb'.
           reflexivity.
    + simpl.
      remember (i <? n) as b''.
      destruct b''.
      * simpl.
        symmetry in Heqb'.
        rewrite Nat.ltb_nlt in Heqb'.
        symmetry in Heqb''.
        rewrite Nat.ltb_lt in Heqb''.
        apply Nat.lt_lt_add_r with (p := m) in Heqb''.
        apply Nat.lt_lt_succ_r in Heqb''.
        apply Heqb' in Heqb''.
        destruct Heqb''.
      * simpl.
        symmetry in Heqb'.
        rewrite Nat.ltb_ge in Heqb'.
        destruct i.
        ** simpl.
           symmetry in Heqb.
           rewrite Nat.eqb_neq in Heqb.
           symmetry in Heqb''.
           rewrite Nat.ltb_ge in Heqb''.
           inversion Heqb''.
           symmetry in H.
           apply Heqb in H.
           destruct H.
        ** rewrite Nat.add_comm with (S i) 1.
           simpl (1 + S i).
           assert (~(S (S i) = n)).
           { rewrite <- Nat.succ_le_mono in Heqb'.
             rewrite <- Nat.lt_succ_r in Heqb'.
             apply Nat.lt_lt_succ_r in Heqb'.
             assert (n <= n + m) by apply Nat.le_add_r.
             assert (n < S (S i)).
             { apply Nat.le_lt_trans with (m := n + m); auto. }
             apply Nat.lt_neq in H0.
             unfold not.
             intros.
             symmetry in H1.
             apply H0 in H1.
             apply H1. }
           assert (n <= n + m) by apply Nat.le_add_r.
           assert (n < S (S i)).
           { apply Nat.le_lt_trans with (m := n + m); auto. }
           rewrite <- Nat.eqb_neq in H.
           rewrite H.
           simpl.
           rewrite Nat.sub_0_r.
           rewrite <- Nat.succ_le_mono in Heqb'.
           rewrite <- Nat.ltb_ge in Heqb'.
           rewrite Heqb'.
           apply Nat.lt_asymm in H1.
           apply Nat.ltb_nlt in H1.
           rewrite H1.
           rewrite Nat.add_comm.
           reflexivity.
  (* Ty_Ref *)
  - simpl.
    rewrite IHT1.
    auto.
Qed.

Lemma tshift_tsubst' : forall n m T1 T2,
    tshift 1 n (tsubst (n + m) T1 T2)
    =
    tsubst (S (n + m)) (tshift 1 n T1) (tshift 1 n T2).
Proof.
  intros.
  generalize dependent n.
  generalize dependent m.
  generalize dependent T1.
  induction T2; intros; auto;
  try( simpl;
       rewrite IHT2_1;
       rewrite IHT2_2;
       reflexivity).
  (* Ty_Var *)
  - simpl.
    remember (i =? n + m) as a.
    symmetry in Heqa.
    destruct a.
    + remember (i <? n) as b.
      symmetry in Heqb.
      destruct b.
      * rewrite Nat.ltb_lt in Heqb.
        rewrite Nat.eqb_eq in Heqa.
        rewrite Heqa in Heqb.
        rewrite Nat.lt_add_lt_sub_l in Heqb.
        rewrite Nat.sub_diag in Heqb.
        apply Nat.nlt_0_r in Heqb.
        destruct Heqb.
      * simpl.
        rewrite Nat.add_comm.
        simpl.
        rewrite Heqa.
        reflexivity.
    + simpl.
      remember (i <? n) as b.
      symmetry in Heqb.
      destruct b.
      * simpl.
        assert (i < n + m)
          by (rewrite Nat.ltb_lt in Heqb;
              apply Nat.lt_lt_add_r with (p := m) in Heqb;
              apply Heqb).
        rewrite <- Nat.ltb_lt in H.
        rewrite H.
        simpl.
        assert (i < S (n + m))
          by (rewrite Nat.ltb_lt in H;
              apply Nat.lt_lt_succ_r in H;
              apply H).
        rewrite <- Nat.ltb_lt in H0.
        rewrite H0.
        simpl.
        assert (i <> S (n + m))
          by (rewrite Nat.ltb_lt in H0;
              apply Nat.lt_neq in H0;
              apply H0).
        rewrite <- Nat.eqb_neq in H1.
        rewrite H1.
        rewrite Heqb.
        reflexivity.
      * simpl.
        rewrite Nat.add_comm with i 1.
        simpl.
        rewrite Heqa.
        remember (i <? n + m) as c.
        symmetry in Heqc.
        destruct c.
        ** simpl.
           rewrite Heqb.
           assert (S i < S (n + m))
             by (rewrite Nat.ltb_lt in Heqc;
                 rewrite Nat.succ_lt_mono in Heqc;
                 apply Heqc).
           rewrite <- Nat.ltb_lt in H.
           rewrite H.
           rewrite Nat.add_comm.
           reflexivity.
        ** simpl.
           assert  (S (n + m) <= S i)
             by (rewrite Nat.ltb_ge in Heqc;
                 apply Nat.succ_le_mono in Heqc;
                 apply Heqc).
           rewrite <- Nat.ltb_ge in H.
           rewrite H.
           rewrite Nat.ltb_ge in Heqb.
           remember (i - 1 <? n) as d.
           destruct d.
           *** destruct i.
               **** reflexivity.
               **** simpl in Heqd.
                    rewrite Nat.sub_0_r in Heqd.
                    symmetry in Heqd.
                    rewrite Nat.ltb_lt in Heqd.
                    simpl.
                    rewrite Nat.eqb_neq in Heqa.
                    assert (n = S i).
                    { rewrite <- Nat.le_succ_l in Heqd.
                      apply Nat.le_antisymm; auto. }
                    rewrite H0 in Heqc.
                    rewrite Nat.ltb_ge in Heqc.
                    assert (m = 0).
                    { apply Nat.le_0_r.
                      apply Nat.add_le_mono_r with (p := S i).
                      simpl.
                      rewrite Nat.add_comm.
                      apply Heqc. }
                    rewrite H1 in Heqa.
                    rewrite H0 in Heqa.
                    rewrite Nat.add_comm in Heqa.
                    simpl in Heqa.
                    destruct Heqa.
                    reflexivity.
           *** rewrite Nat.sub_0_r.
               assert (i - 1 + 1 = i).
               { destruct i.
                 - simpl.
                   rewrite Nat.eqb_neq in Heqa.
                   rewrite Nat.ltb_ge in Heqc.
                   inversion Heqc.
                   symmetry in H1.
                   apply Heqa in H1.
                   destruct H1.
                 - simpl.
                   rewrite Nat.sub_0_r.
                   rewrite Nat.add_comm.
                   reflexivity. }
               rewrite H0.
               reflexivity.
  (* Ty_Forall *)
  - simpl.
    assert (n = 0 + n) by auto.
    rewrite H.
    rewrite tshift_tshift.
    simpl.
    specialize IHT2 with (n := S n).
    simpl in IHT2.
    rewrite IHT2.
    reflexivity.
  (* Ty_Some *)
  - simpl.
    specialize IHT2 with (n := S n).
    simpl in IHT2.
    rewrite IHT2.
    rewrite tshift_tshift_0.
    reflexivity.
  (* Ty_Rec *)
  - simpl.
    specialize IHT2 with (n := S n).
    simpl in IHT2.
    rewrite IHT2.
    rewrite tshift_tshift_0.
    reflexivity.
  (* Ty_Ref *)
  - simpl.
    rewrite IHT2.
    auto.
Qed.

Corollary tshift_tsubst'_0 : forall n T1 T2,
    tshift 1 0 (tsubst n T1 T2)
    =
    tsubst (S n) (tshift 1 0 T1) (tshift 1 0 T2).
Proof.
  intros.
  assert (n = 0 + n) by auto.
  rewrite H.
  rewrite tshift_tsubst'.
  reflexivity.
Qed.

Lemma tsubst_tsubst : forall n m T1 T2 T3,
    tsubst (n + m) T1 (tsubst n T2 T3)
    =
    tsubst n (tsubst (n + m) T1 T2) (tsubst (S (n + m)) (tshift 1 n T1) T3).
Proof.
  intros n m T1 T2 T3.
  generalize dependent n.
  generalize dependent m.
  generalize dependent T1.
  generalize dependent T2.
  induction T3; intros; auto;
    try( simpl;
         rewrite IHT3_1;
         rewrite IHT3_2;
         reflexivity).
  (* Ty_Var *)
  - simpl.
    remember (i =? n) as a.
    destruct a.
    + remember (i =? S (n + m)) as b.
      destruct b.
      * symmetry in Heqa.
        symmetry in Heqb.
        rewrite Nat.eqb_eq in Heqa.
        rewrite Nat.eqb_eq in Heqb.
        assert (n <= n + m).
        { apply Nat.le_add_r. }
        assert (n < S (n + m)).
        { apply Nat.lt_succ_r.
          apply H. }
        rewrite Heqa in Heqb.
        apply Nat.lt_neq in H0.
        apply H0 in Heqb.
        destruct Heqb.
      * simpl.
        symmetry in Heqa.
        symmetry in Heqb.
        assert (n <= n + m).
        { apply Nat.le_add_r. }
        assert (n < S (n + m)).
        { apply Nat.lt_succ_r.
          apply H. }
        rewrite Nat.eqb_eq in Heqa.
        rewrite <- Nat.ltb_lt in H0.
        rewrite Heqa.
        rewrite H0.
        simpl.
        rewrite Nat.eqb_refl.
        reflexivity.
    + remember (i <? n) as b.
      destruct b.
      * assert (i < S (n + m)).
        { symmetry in Heqb.
          rewrite Nat.ltb_lt in Heqb.
          apply Nat.lt_lt_add_r with (p := m) in Heqb.
          apply Nat.lt_lt_succ_r in Heqb.
          auto. }
        rewrite <- Nat.ltb_lt in H.
        rewrite H.
        rewrite Nat.ltb_lt in H.
        apply Nat.lt_neq in H.
        rewrite <- Nat.eqb_neq in H.
        rewrite H.
        simpl.
        rewrite <- Heqa.
        rewrite <- Heqb.
        assert (i <> n + m).
        { symmetry in Heqb.
          rewrite Nat.ltb_lt in Heqb.
          apply Nat.lt_lt_add_r with (p := m) in Heqb.
          apply Nat.lt_neq.
          apply Heqb. }
        rewrite <- Nat.eqb_neq in H0.
        rewrite H0.
        symmetry in Heqb.
        rewrite Nat.ltb_lt in Heqb.
        apply Nat.lt_lt_add_r with (p := m) in Heqb.
        rewrite <- Nat.ltb_lt in Heqb.
        rewrite Heqb.
        reflexivity.
      * remember (i =? S (n + m)) as c.
        destruct c.
        ** simpl.
           symmetry in Heqc.
           rewrite Nat.eqb_eq in Heqc.
           rewrite Heqc.
           simpl.
           rewrite Nat.sub_0_r.
           rewrite Nat.eqb_refl.
           simpl.
           rewrite tsubst_tshift.
           reflexivity.
        ** simpl.
           symmetry in Heqc.
           rewrite Nat.eqb_neq in Heqc.
           destruct i.
           *** symmetry in Heqb.
               symmetry in Heqa.
               rewrite Nat.eqb_neq in Heqa.
               rewrite Nat.ltb_ge in Heqb.
               rewrite Nat.le_0_r in Heqb.
               symmetry in Heqb.
               apply Heqa in Heqb.
               destruct Heqb.
           *** simpl.
               rewrite Nat.sub_0_r.
               remember (i <? n + m) as d.
               rewrite Nat.succ_inj_wd_neg in Heqc.
               rewrite <- Nat.eqb_neq in Heqc.
               rewrite Heqc.
               destruct d.
               **** symmetry in Heqd.
                    rewrite Nat.ltb_lt in Heqd.
                    apply Nat.lt_succ_r in Heqd.
                    rewrite <- Nat.ltb_lt in Heqd.
                    rewrite Heqd.
                    simpl.
                    rewrite <- Heqb.
                    rewrite Nat.sub_0_r.
                    destruct n; auto.
                    symmetry in Heqa.
                    rewrite Nat.eqb_neq in Heqa.
                    rewrite Nat.succ_inj_wd_neg in Heqa.
                    rewrite <- Nat.eqb_neq in Heqa.
                    rewrite Heqa.
                    reflexivity.
               **** symmetry in Heqd.
                    assert  (S (n + m) <= S i).
                    { rewrite Nat.ltb_ge in Heqd.
                      apply Nat.lt_succ_r in Heqd.
                      apply Nat.le_succ_l in Heqd.
                      auto. }
                    rewrite <- Nat.ltb_ge in H.
                    rewrite H.
                    simpl.
                    rewrite Nat.ltb_ge in Heqd.
                    rewrite Nat.eqb_neq in Heqc.
                    assert (n + m < i) by (apply Nat.le_neq; auto).
                    assert (n <= i).
                    { apply Nat.le_trans with (m := n + m); auto.
                      apply Nat.le_add_r. }
                    rewrite <- Nat.ltb_ge in H1.
                    rewrite H1.
                    assert (n < i).
                    { apply Nat.le_lt_trans with (m := n + m); auto.
                      apply Nat.le_add_r. }
                    apply Nat.lt_neq in H2.
                    rewrite <- Nat.eqb_neq in H2.
                    rewrite Nat.eqb_sym.
                    rewrite H2.
                    reflexivity.
  (* Ty_Forall *)
  - simpl.
    specialize IHT3 with (n := S n).
    simpl in IHT3.
    rewrite IHT3.
    assert (n = 0 + n) by auto.
    rewrite H.
    rewrite <- tshift_tshift.
    simpl.
    assert (S (n + m) = S (0 + (n + m))) by auto.
    rewrite H0.
    rewrite <- tshift_tsubst'.
    simpl.
    reflexivity.
  (* Ty_Some *)
  - simpl.
    specialize IHT3 with (n := S n).
    simpl in IHT3.
    rewrite IHT3.
    simpl.
    rewrite tshift_tshift_0.
    rewrite tshift_tsubst'_0.
    reflexivity.
  (* Ty_Rec *)
  - simpl.
    specialize IHT3 with (n := S n).
    simpl in IHT3.
    rewrite IHT3.
    simpl.
    rewrite tshift_tshift_0.
    rewrite tshift_tsubst'_0.
    reflexivity.
  (* Ty_Ref *)
  - simpl.
    rewrite IHT3.
    auto.
Qed.

Corollary tsubst_tsubst_0 : forall n T1 T2 T3,
    tsubst n T1 (tsubst 0 T2 T3)
    =
    tsubst 0 (tsubst n T1 T2) (tsubst (S n) (tshift 1 0 T1) T3).
Proof.
  intros.
  assert (n = 0 + n) by auto.
  rewrite H.
  rewrite tsubst_tsubst.
  reflexivity.
Qed.

Corollary tshift_tsubst_0 : forall n T1 T2,
    tshift 1 n (tsubst 0 T2 T1)
    =
    tsubst 0 (tshift 1 n T2) (tshift 1 (S n) T1).
Proof.
  intros.
  assert (n = 0 + n) by auto.
  rewrite H.
  rewrite tshift_tsubst.
  reflexivity.
Qed.

           
Corollary tshift_tsubst_gamma : forall n m T Γ,
    map (tshift 1 n) (map (tsubst (n + m) T) Γ)
    =
    map (tsubst (S (n + m)) (tshift 1 n T)) (map (tshift 1 n) Γ).
Proof.
  intros.
  generalize dependent n.
  generalize dependent m.
  generalize dependent T.
  induction Γ; intros; auto.
  simpl.
  rewrite IHΓ.
  rewrite tshift_tsubst'.
  reflexivity.
Qed.

Corollary tshift_tshift_gamma : forall n m Γ,
    map (tshift 1 n) (map (tshift 1 (n + m)) Γ)
    =
    map (tshift 1 (S (n + m))) (map (tshift 1 n) Γ).
Proof.
  intros.
  generalize dependent n.
  generalize dependent m.
  induction Γ; intros.
  - simpl.
    reflexivity.
  - simpl.
    rewrite tshift_tshift.
    rewrite IHΓ.
    reflexivity.
Qed.

Corollary tshift_tshift_gamma_0 : forall n Γ,
    map (tshift 1 0) (map (tshift 1 n) Γ)
    =
    map (tshift 1 (S n)) (map (tshift 1 0) Γ).
Proof.
  intros.
  assert (n = 0 + n) by auto.
  rewrite H.
  rewrite tshift_tshift_gamma.
  reflexivity.
Qed.
    
Lemma shift_preservation : forall (Σ Γ1 Γ2 Δ : context) (T : ty) (e : expr),
    has_type Σ (Γ1 ++ Γ2) e T ->
    has_type Σ (Γ1 ++ Δ ++ Γ2) (shift (length Δ) (length Γ1) e) T.
Proof.
  intros.
  remember (Γ1 ++ Γ2) as Γ eqn:HeqG.
  revert Γ1 Γ2 HeqG.
  generalize dependent Δ.
  induction H; intros; auto.
  (* T_Var *)
  - simpl.
    remember (k <? length Γ1) as b eqn:Heqb.
    symmetry in Heqb.
    destruct b; apply T_Var.
    (* k < length Γ1 *)
    + apply Nat.ltb_lt in Heqb.
      rewrite HeqG in H.
      rewrite nth_error_app1 in H; auto.
      rewrite <- H.
      apply nth_error_app1.
      assumption.
    (* length Γ1 <= k *)
    + apply Nat.ltb_ge in Heqb.
      rewrite HeqG in H.
      rewrite nth_error_app2 in H; auto.
      rewrite <- H.
      assert (nth_error ((Γ1 ++ Δ) ++ Γ2) (k + length Δ)
              = nth_error Γ2 ((k + length Δ) - length (Γ1 ++ Δ))).
      { apply nth_error_app2.
        rewrite app_length.
        apply Nat.add_le_mono_r.
        assumption. }
      rewrite <- app_assoc in H0.
      rewrite H0.
      rewrite app_length.
      rewrite Nat.add_comm.
      rewrite Nat.add_comm with (length Γ1) (length Δ).
      rewrite <- Minus.minus_plus_simpl_l_reverse.
      reflexivity.
  (* T_App  *)
  - simpl.
    econstructor.
    + apply IHhas_type1; auto.
    + apply IHhas_type2; auto.
  (* T_Rec  *)
  - simpl.
    constructor.
    assert (<{{ T2 -> T1 }}> :: T2 :: Γ = (<{{ T2 -> T1 }}> :: T2 :: Γ1) ++ Γ2)
      by (simpl; rewrite HeqG; auto).
    eapply IHhas_type in H0.
    simpl in H0.
    apply H0.
  (* T_If *)
  - simpl.
    constructor.
    + apply IHhas_type1; auto.
    + apply IHhas_type2; auto.
    + apply IHhas_type3; auto.
  (* T_Int  *)
  - simpl.
    constructor.
  (* T_Binop *)
  - simpl.
    econstructor.
    + apply H.
    + apply IHhas_type1; auto.
    + apply IHhas_type2; auto.
  (* T_Pair *)
  - simpl.
    constructor.
    + apply IHhas_type1; auto.
    + apply IHhas_type2; auto.
  (* T_Fst *)
  - simpl.
    econstructor.
    apply IHhas_type; auto.
  (* T_Snd *)
  - simpl.
    econstructor.
    apply IHhas_type; auto.
  (* T_Inl *)
  - simpl.
    constructor.
    apply IHhas_type; auto.
  (* T_Inr *)
  - simpl.
    constructor.
    apply IHhas_type; auto.
  (* T_Case *)
  - simpl.
    econstructor.
    + apply IHhas_type1; auto.
    + assert (T1 :: Γ = (T1 :: Γ1) ++ Γ2) by (simpl; rewrite HeqG; auto).
      eapply IHhas_type2 in H2; eauto.
    + assert (T2 :: Γ = (T2 :: Γ1) ++ Γ2) by (simpl; rewrite HeqG; auto).
      eapply IHhas_type3 in H2; eauto.
  (* T_TAbs *)
  - simpl.
    constructor.
    repeat rewrite map_app.
    specialize IHhas_type with (Δ := map (tshift 1 0) Δ).
    specialize IHhas_type with (Γ1 := map (tshift 1 0) Γ1).
    specialize IHhas_type with (Γ2 := map (tshift 1 0) Γ2).
    do 2 rewrite map_length in IHhas_type.
    apply IHhas_type.
    rewrite HeqG.
    rewrite map_app.
    reflexivity. 
  (* T_TApp *)
  - simpl.
    constructor.
    apply IHhas_type.
    apply HeqG.
  (* T_Pack *)
  - simpl.
    econstructor.
    apply IHhas_type; auto.
  (* T_Unpack *)
  - simpl.
    econstructor; eauto.
    do 2 rewrite map_app.
    specialize IHhas_type2 with (Γ1 := T1 :: (map (tshift 1 0) Γ1)).
    simpl in IHhas_type2.
    specialize IHhas_type2 with (Γ2 := map (tshift 1 0) Γ2).
    specialize IHhas_type2 with (Δ := map (tshift 1 0) Δ).
    simpl in IHhas_type2.
    do 2 rewrite map_length in IHhas_type2.
    apply IHhas_type2.
    rewrite HeqG.
    rewrite map_app.
    reflexivity.
  (* T_Fold *)
  - simpl.
    constructor.
    apply IHhas_type; auto.
  (* T_Unfold *)
  - simpl.
    constructor.
    apply IHhas_type; auto.
  (* T_Loc *)
  - simpl.
    apply T_Loc.
    apply H.
  (* T_Alloc *)
  - simpl.
    constructor.
    apply IHhas_type; auto.
  (* T_Assign *)
  - simpl.
    econstructor; eauto.
  (* T_Load *)
  - simpl.
    constructor; eauto.
Qed.

Lemma tshift_preservation : forall n Σ Γ e T,
    has_type Σ Γ e T -> has_type (map (tshift 1 n) Σ) (map (tshift 1 n) Γ) e (tshift 1 n T).
Proof.
  intros.
  generalize dependent n.
  induction H; intros; auto.
  (* T_Var *)
  - simpl.
    constructor.
    simpl.
    apply map_nth_error; auto.
  (* T_App *)
  - simpl.
    econstructor.
    + apply IHhas_type1.
    + apply IHhas_type2.
  (* T_Rec *)
  - simpl.
    constructor.
    apply IHhas_type.
  (* T_If *)
  - simpl.
    constructor;
      [apply IHhas_type1
      |apply IHhas_type2
      |apply IHhas_type3].
  (* T_Binop *)
  - simpl.
    destruct bop0;
      inversion H;
      subst;
      simpl;
      econstructor;
      simpl in IHhas_type1;
      simpl in IHhas_type2;
      eauto.
  (* T_Pair *)
  - simpl;
      constructor;
      [apply IHhas_type1
      |apply IHhas_type2].
  (* T_Fst *)
  - simpl;
      econstructor;
      eauto.
  (* T_Snd *)
  - simpl;
      econstructor;
      eauto.
  (* T_Inl *)
  - simpl;
      constructor;
      auto.
  (* T_Inr *)
  - simpl;
      constructor;
      auto.
  (* T_Case *)
  - simpl;
      econstructor;
      [apply IHhas_type1
      |apply IHhas_type2
      |apply IHhas_type3].
  (* T_TAbs *)
  - simpl.
    constructor.
    assert (n = 0 + n) by auto.
    rewrite H0.
    do 2 rewrite tshift_tshift_gamma.
    simpl.
    apply IHhas_type.
  (* T_TApp *)
  - simpl.
    assert (n = 0 + n) by auto.
    rewrite H0.
    rewrite tshift_tsubst.
    simpl.
    simpl in IHhas_type.
    constructor.
    apply IHhas_type.
  (* T_Pack *)
  - simpl.
    apply T_Pack with (T1 := (tshift 1 n T1)).
    assert (n = 0 + n) by auto.
    rewrite H0.
    rewrite <- tshift_tsubst.
    simpl.
    apply IHhas_type.
  (* T_Unpack *)
  - simpl.
    econstructor; eauto.
    do 2 rewrite tshift_tshift_gamma_0.
    rewrite tshift_tshift_0.
    simpl in IHhas_type2.
    apply IHhas_type2.
  (* T_Fold *)
  - constructor.
    specialize IHhas_type with (n := n).
    rewrite tshift_tsubst_0 in IHhas_type.
    simpl in IHhas_type.
    apply IHhas_type.
  (* T_Unfold *)
  - rewrite tshift_tsubst_0.
    constructor.
    apply IHhas_type.
  (* T_Loc *)
  - simpl.
    rewrite store_lookup_shift; auto.
    apply T_Loc.
    rewrite map_length.
    apply H.
  (* T_Alloc *)
  - simpl.
    constructor.
    apply IHhas_type.
  (* T_Assign *)
  - simpl.
    econstructor; eauto.
  (* T_Load *)
  - constructor.
    apply IHhas_type.
Qed.

    
Lemma subst_preservation : forall Σ Γ1 Γ2 T1 T2 e1 e2,
    has_type Σ (Γ1 ++ T2 :: Γ2) e1 T1 ->
    has_type Σ (Γ1 ++ Γ2) e2 T2 ->
    has_type Σ (Γ1 ++ Γ2) (subst (length Γ1) e2 e1) T1.
Proof.
  intros.
  remember (Γ1 ++ T2 :: Γ2) as Γ eqn:HeqG.
  generalize dependent e2.
  revert Γ1 Γ2 HeqG.
  generalize dependent T2.
  induction H;
    intros;
    try (econstructor; eauto; assumption);
    simpl; auto.
  (* T_Var *)
  - remember (k =? length Γ1) as b eqn:Heqb.
    symmetry in Heqb.
    destruct b.
    + rewrite Nat.eqb_eq in Heqb.
      rewrite HeqG in H.
      rewrite Heqb in H.
      assert (nth_error (Γ1 ++ T2 :: Γ2) (length Γ1)
              = nth_error (T2 :: Γ2) (length Γ1 - length Γ1))
        by (apply nth_error_app2; auto).
      rewrite Nat.sub_diag in H1.
      rewrite H1 in H.
      simpl in H.
      inversion H.
      rewrite H3 in H0.
      assumption.
    + remember (k <? length Γ1) as b' eqn:Heqb'.
      symmetry in Heqb'.
      destruct b'.
      * apply T_Var.
        apply Nat.ltb_lt in Heqb'.
        remember Heqb' as H'; clear HeqH'.
        apply nth_error_app1 with (l':=Γ2) in H'.
        apply nth_error_app1 with (l':=(T2::Γ2)) in Heqb'.
        rewrite HeqG in H.
        rewrite <- Heqb' in H'.
        rewrite H in H'.
        apply H'.
      * apply T_Var.
        rewrite HeqG in H.
        assert (nth_error (T2::Γ2) (k - length Γ1) = nth_error (Γ1 ++ T2 :: Γ2) k).
        { symmetry.
          apply nth_error_app2.
          apply Nat.ltb_ge.
          apply Heqb'. }
        assert (nth_error (T2 :: Γ2) (k - length Γ1) = nth_error Γ2 ((k - length Γ1) - 1)).
        { assert ((T2 :: empty) ++ Γ2 = T2 :: Γ2) by auto.
          rewrite <- H2.
          apply nth_error_app2.
          simpl.
          apply Nat.ltb_ge in Heqb'.
          inversion Heqb'.
          - rewrite Nat.eqb_neq in Heqb.
            destruct Heqb.
            symmetry.
            apply H3.
          - rewrite Nat.sub_succ_l; auto.
            apply le_n_S.
            apply Nat.le_0_l. }
        assert (nth_error (Γ1 ++ Γ2) (k - 1) = nth_error Γ2 (k - 1 - length Γ1)).
        { apply nth_error_app2.
          rewrite Nat.ltb_ge in Heqb'.
          inversion Heqb'.
          - rewrite Nat.eqb_neq in Heqb.
            destruct Heqb.
            symmetry.
            apply H3.
          - rewrite Nat.sub_succ.
            rewrite Nat.sub_0_r.
            apply H3. }
        assert (k - length Γ1 - 1 = k - 1 - length Γ1).
        { do 2 rewrite <- Nat.sub_add_distr.
          rewrite Nat.add_comm.
          auto. }
        rewrite <- H1 in H.
        rewrite H2 in H.
        rewrite H4 in H.
        rewrite <- H3 in H.
        apply H.
  (* T_Rec *)
  - apply T_Rec.
    assert (<{{ T2 -> T1 }}> :: T2 :: Γ
            = (<{{ T2 -> T1 }}> :: T2 :: Γ1) ++ (T0 :: Γ2))
      by (rewrite HeqG; auto).
    eapply IHhas_type in H1.
    + apply H1.
    + simpl.
      assert (<{{ T2 -> T1 }}> :: T2 :: Γ1 ++ Γ2 =
              empty ++ (<{{ T2 -> T1 }}> :: T2 :: empty) ++ (Γ1 ++ Γ2))
        by (symmetry; auto).
      rewrite H2.
      apply shift_preservation.
      simpl.
      apply H0.
  (* T_Case *)
  - eapply T_Case; eauto.
    + assert (T1 :: Γ = (T1 :: Γ1) ++ (T0 :: Γ2)) by (rewrite HeqG; auto).
      eapply IHhas_type2 in H3.
      * apply H3.
      * simpl.
        assert (T1 :: Γ1 ++ Γ2 = empty ++ (T1 :: empty) ++ (Γ1 ++ Γ2)) by (symmetry; auto).
        rewrite H4.
        apply shift_preservation.
        apply H2.
    + assert (T2 :: Γ = (T2 :: Γ1) ++ (T0 :: Γ2)) by (rewrite HeqG; auto).
      eapply IHhas_type3 in H3.
      * apply H3.
      * simpl.
        assert (T2 :: Γ1 ++ Γ2 = empty ++ (T2 :: empty) ++ (Γ1 ++ Γ2)) by (symmetry; auto).
        rewrite H4.
        apply shift_preservation.
        apply H2.
  (* T_TAbs *)
  - simpl.
    assert (map (tshift 1 0) Γ =
            (map (tshift 1 0) Γ1) ++ (tshift 1 0 T2) :: (map (tshift 1 0) Γ2)).
    { rewrite HeqG.
      rewrite map_app.
      simpl.
      reflexivity. }
    eapply IHhas_type in H1.
    + constructor.
      rewrite map_app.
      rewrite map_length in H1.
      apply H1.
    + rewrite <- map_app.
      specialize IHhas_type with (T2 := (tshift 1 0 T2)).
      specialize IHhas_type with (Γ2 := map (tshift 1 0) Γ2).
      apply tshift_preservation.
      apply H0.
  (* T_Unpack *)    
  - econstructor.
    eapply IHhas_type1.
    apply HeqG.
    apply H1.
    specialize IHhas_type2 with (Γ1 := T1 :: map (tshift 1 0) Γ1).
    specialize IHhas_type2 with (Γ2 := map (tshift 1 0) Γ2).
    specialize IHhas_type2 with (T3 := tshift 1 0 T0).
    simpl in IHhas_type2.
    rewrite map_app.
    rewrite map_length in IHhas_type2.
    apply IHhas_type2.
    + rewrite HeqG.
      rewrite map_app.
      simpl.
      reflexivity.
    + rewrite <- map_app.
      assert (T1 :: map (tshift 1 0) (Γ1 ++ Γ2) =
              empty ++ (T1 :: empty) ++ map (tshift 1 0) (Γ1 ++ Γ2)) by auto.
      rewrite H2.
      apply shift_preservation.
      simpl.
      apply tshift_preservation.
      apply H1.
Qed.


Lemma tsubst_preservation : forall e T T' Σ Γ n,
    has_type Σ Γ e T -> has_type (map (tsubst n T') Σ) (map (tsubst n T') Γ) e (tsubst n T' T).
Proof.
  intros.
  generalize dependent T'.
  generalize dependent n.
  induction H; intros; simpl; auto.
  (* T_Var *)
  - intros.
    simpl.
    constructor.
    apply map_nth_error.
    auto.
  (* T_App *)
  - intros.
    simpl.
    apply T_App with <{{ [| @ n / T'|] T2 }}>.
    + apply IHhas_type1.
    + apply IHhas_type2.
  (* T_Rec *)
  - intros.
    simpl.
    constructor.
    apply IHhas_type.
  (* T_If *)
  - constructor.
    + apply IHhas_type1.
    + apply IHhas_type2.
    + apply IHhas_type3.
  (* T_Binop *)
  - destruct bop0; inversion H; subst; simpl;
      apply T_Binop with (T1 := <{{ Int }}>) (T2 := <{{ Int }}>); eauto.
  (* T_Fst *)
  - apply T_Fst with (T2 := <{{ [| @ n / T'|] T2 }}>); eauto.
  (* T_Snd *)
  - apply T_Snd with (T1 := <{{ [| @ n / T'|] T1 }}>); eauto.
  (* T_Case *)
  - apply T_Case with (T1 := <{{ [| @ n / T'|] T1 }}>)
                      (T2 := <{{ [| @ n / T'|] T2 }}>); eauto.
  (* T_TAbs *)
  - constructor.
    specialize IHhas_type with (n := S n).
    specialize IHhas_type with (T' := (tshift 1 0 T')).
    assert (n = (0 + n)) by auto.
    rewrite H0.
    do 2 rewrite tshift_tsubst_gamma.
    simpl.
    apply IHhas_type.
  (* T_TApp *)
  - assert (n = (0 + n)) by auto.
    rewrite H0.
    rewrite tsubst_tsubst.
    simpl.
    constructor.
    apply IHhas_type.
  (* T_Pack *)
  - apply T_Pack with (T1 := tsubst n T' T1).
    assert (n = 0 + n) by auto.
    rewrite H0.
    rewrite <- tsubst_tsubst.
    simpl.
    apply IHhas_type.
  (* T_Unpack *)
  - econstructor; eauto.
    rewrite tshift_tsubst'_0.
    specialize IHhas_type2 with (n := S n).
    specialize IHhas_type2 with (T' := tshift 1 0 T').
    simpl in IHhas_type2.
    fold tsubst.
    assert (n = 0 + n) by auto.
    rewrite H1.
    do 2 rewrite tshift_tsubst_gamma.
    simpl.
    apply IHhas_type2.
  (* T_Fold *)
  - constructor.
    assert (Ty_Rec (tsubst (S n) (tshift 1 0 T') T) = (tsubst n T' (Ty_Rec T))) by auto.
    rewrite H0.
    rewrite <- tsubst_tsubst_0.
    simpl.
    apply IHhas_type.
  (* T_Unfold *)
  - rewrite tsubst_tsubst_0.
    constructor.
    apply IHhas_type.
  (* T_Loc *)
  - rewrite store_lookup_subst; auto.
    constructor.
    rewrite map_length.
    apply H.
  (* T_Assign *)
  - econstructor; eauto.
  (* T_Load *)
  - econstructor; eauto. 
Qed.
