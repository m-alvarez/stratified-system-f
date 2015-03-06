Require Import Arith.
Require Import Arith.Max.
Require Import Arith.Compare_dec.
Require Import Omega.
Require Import Lt.
Require Import Bool.

Add LoadPath ".".

Require Import SysF.

Lemma beq_typ_correct : forall t1 t2 : typ, beq_typ t1 t2 = true -> t1 = t2. 
  induction t1.
  - intros.
    destruct t2; [ auto using beq_nat_eq | inversion H .. ].
  - intros.
    destruct t2.
    + inversion H.
    + apply andb_true_iff in H. 
      destruct H.
      apply IHt1_1 in H.
      apply IHt1_2 in H0. 
      congruence.
    + inversion H.
  - intros.
    destruct t2.
    + inversion H.
    + inversion H.
    + apply andb_true_iff in H.
      destruct H.
      apply IHt1 in H0.
      apply eq_sym in H. apply beq_nat_eq in H.
      congruence.
Qed.

Lemma beq_typ_refl : forall t : typ, beq_typ t t = true.
  intro.
  induction t.
  - apply eq_sym. apply beq_nat_refl.
  - apply andb_true_iff. split. apply IHt1. apply IHt2.
  - apply andb_true_iff. split. symmetry. apply beq_nat_refl. apply IHt.
Qed.

(* This is actually cumulativity *)
Lemma kinding_sub : forall (e : env) (t : typ) (k : kind),
                          kinding e t k -> forall k', k <= k' -> kinding e t k'.
  do 4 intro.
  induction H.
  - intros.
    assert (p <= k') by omega.
    eauto using k_tvar.
  - intros.
    destruct k'.
    + inversion H0.
    + assert (max p q <= k') by omega.
      assert (max k' q = k') by eauto with arith.
      rewrite <- H2.
      eauto using k_tall with arith.
  - intros.
    assert (p <= max p q /\ q <= max p q) by auto with arith.
    assert (max k' k' = k') by auto with arith.
    rewrite <- H3.
    destruct H2.
    apply k_tarr; [ eauto using le_trans .. ]. (* TODO just eauto using k_tarr, le_trans doesn't work *)
Qed.

Definition cumulativity := kinding_sub.


(* TODO simplified the equivalences to implications so this plays nice with eauto *)
Lemma bwf_typ_correct : forall t : typ, forall e : env, bwf_typ e t = true -> wf_typ e t.
  induction t.
  - intro. simpl.
    destruct (get_kind e n); [ intuition .. ]. discriminate.
  - intros.
    apply andb_true_iff in H.
    split.
    + apply IHt1. apply H.
    + apply IHt2. apply H.
  - intro. apply IHt.
Qed.

Lemma bwf_typ_complete : forall (t : typ) (e : env), wf_typ e t -> bwf_typ e t = true.
  induction t; simpl; auto; intros.
  - destruct (get_kind e n); auto.
  - apply andb_true_iff. split; [apply IHt1 | apply IHt2]; destruct H; auto.
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

Theorem kind_of_correct (t : typ) : 
  forall (e : env) (k : kind), 
    kind_of e t = Some k -> kinding e t k.
  induction t.
  - intros. simpl in H.
    remember (bwf_env e).
    destruct b.
    + apply eq_sym in Heqb. eauto using bwf_env_correct, k_tvar.
    + discriminate H.
  - intros. simpl in H.
    remember (kind_of e t1) as kind_of_t1.
    remember (kind_of e t2) as kind_of_t2.
    destruct kind_of_t1, kind_of_t2;
      [ inversion H; eauto using k_tarr | inversion H .. ].
  - intros. simpl in H.
    destruct (kind_of (etvar k e) t) eqn:kind_of_etvar.
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
