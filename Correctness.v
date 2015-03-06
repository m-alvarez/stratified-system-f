Require Import Arith.
Require Import Arith.Max.
Require Import Arith.Compare_dec.
Require Import Omega.
Require Import Lt.
Require Import Bool.

Add LoadPath ".".

Require Import SysF.

Lemma beq_typ_correct : forall T1 T2 : typ, beq_typ T1 T2 = true -> T1 = T2.
  induction T1.
  - intros.
    destruct T2; [ auto using beq_nat_eq | inversion H .. ].
  - intros.
    destruct T2.
    + inversion H.
    + apply andb_true_iff in H. 
      destruct H.
      apply IHT1_1 in H.
      apply IHT1_2 in H0. 
      congruence.
    + inversion H.
  - intros.
    destruct T2.
    + inversion H.
    + inversion H.
    + apply andb_true_iff in H.
      destruct H.
      apply IHT1 in H0.
      apply eq_sym in H. apply beq_nat_eq in H.
      congruence.
Qed.

Lemma beq_typ_refl : forall T : typ, beq_typ T T = true.
  intro.
  induction T.
  - apply eq_sym. apply beq_nat_refl.
  - apply andb_true_iff. split. apply IHT1. apply IHT2.
  - apply andb_true_iff. split. symmetry. apply beq_nat_refl. apply IHT.
Qed.

(* This is actually cumulativity *)
Lemma kinding_sub : forall (e : env) (T : typ) (K : kind),
                          kinding e T K -> forall K', K <= K' -> kinding e T K'.
  do 4 intro.
  induction H.
  - intros.
    assert (Kp <= K') by omega.
    eauto using k_tvar.
  - intros.
    destruct K'.
    + inversion H0.
    + assert (max Kp Kq <= K') by omega.
      assert (max K' Kq = K') by eauto with arith.
      rewrite <- H2.
      eauto using k_tall with arith.
  - intros.
    assert (Kp <= max Kp Kq /\ Kq <= max Kp Kq) by auto with arith.
    assert (max K' K' = K') by auto with arith.
    rewrite <- H3.
    destruct H2.
    apply k_tarr; [ eauto using le_trans .. ]. (* TODO just eauto using k_tarr, le_trans doesn't work *)
Qed.

Definition cumulativity := kinding_sub.


(* TODO simplified the equivalences to implications so this plays nice with eauto *)
Lemma bwf_typ_correct : forall T : typ, forall e : env, bwf_typ e T = true -> wf_typ e T.
  induction T.
  - intro. simpl.
    destruct (get_kind e n); [ intuition .. ]. discriminate.
  - intros.
    apply andb_true_iff in H.
    split.
    + apply IHT1. apply H.
    + apply IHT2. apply H.
  - intro. apply IHT.
Qed.

Lemma bwf_typ_complete : forall (T : typ) (e : env), wf_typ e T -> bwf_typ e T = true.
  induction T; simpl; auto; intros.
  - destruct (get_kind e n); auto.
  - apply andb_true_iff. split; [apply IHT1 | apply IHT2]; destruct H; auto.
Qed. 

Lemma bwf_env_correct : forall e : env, bwf_env e = true -> wf_env e.
  induction e; simpl; auto.
  - intro.
    apply andb_true_iff in H.
    split.
    + apply bwf_typ_correct. apply H.
    + apply IHe. apply H.
Qed.

Lemma bwf_env_complete : forall e : env, wf_env e -> bwf_env e = true.
  induction e; auto.
  - intro. simpl. apply andb_true_iff. split; destruct H; auto using bwf_typ_complete.
Qed.

Theorem kind_of_correct (T : typ) : 
  forall (e : env) (K : kind), 
    kind_of e T = Some K -> kinding e T K.
  induction T.
  - intros. simpl in H.
    remember (bwf_env e).
    destruct b.
    + apply eq_sym in Heqb. eauto using bwf_env_correct, k_tvar.
    + discriminate H.
  - intros. simpl in H.
    remember (kind_of e T1) as kind_of_T1.
    remember (kind_of e T2) as kind_of_T2.
    destruct kind_of_T1, kind_of_T2;
      [ inversion H; eauto using k_tarr | inversion H .. ].
  - intros. simpl in H.
    destruct (kind_of (etvar k e) T) eqn:kind_of_etvar.
    + inversion H. eauto using k_tall.
    + inversion H.
Qed. 

Theorem type_of_correct (t : term) : 
  forall (e : env) (T : typ), 
    type_of e t = Some T -> typing e t T.
  induction t.
  - intros. simpl in H.
    destruct (bwf_env e) eqn:env_is_bwf.
    + auto using t_var, bwf_env_correct.
    + inversion H.
  - intros. simpl in H.
    destruct (type_of (evar t e) t0) eqn:type_of_body.
    + remember (bwf_typ e t). destruct b.
      * inversion H. apply t_abs. apply bwf_typ_correct. auto. apply IHt, type_of_body.
      * discriminate.
    + inversion H.
  - intros. simpl in H.
    destruct (type_of e t1) eqn:type_of_fn.
    + destruct t.
      * inversion H.
      * destruct (type_of e t2) eqn:type_of_arg.
        { destruct (beq_typ t3 t) eqn:equal_types.
          { inversion H. rewrite <- H1.
            eauto. apply beq_typ_correct in equal_types. eapply t_app. eauto. rewrite equal_types. eauto. }
          { inversion H. } }
        { inversion H. }
      * inversion H.
    + inversion H.
  - intros. simpl in H.
    destruct (type_of (etvar k e) t) eqn:type_of_body.
    + inversion H. auto using t_abs_t.
    + inversion H.
  - intros. simpl in H.
    destruct (type_of e t) eqn:?.
    + destruct t1 eqn:type_of_term.
      * inversion H.
      * inversion H.
      * destruct (kind_of e t0) eqn:kind_of_arg.
        { destruct (Arith.Compare_dec.leb k0 k) eqn:k0_leb.
          { inversion H. eapply t_app_t. eauto.
            eauto using kind_of_correct, leb_complete, kinding_sub, t_app_t. }
          { inversion H. } }
        { inversion H. }
    + inversion H.
Qed.
