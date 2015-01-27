Require Import Arith.
Require Import Arith.Max.
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

Theorem leq_correct : forall m n : nat, leq m n = true -> m <= n.
  induction m.
  - auto with arith.
  - intros. destruct n.
    + inversion H.
    + auto with arith.
Qed.

(* This is actually cumulativity *)
Lemma kinding_ind_sub : forall (e : env) (t : typ) (k : kind),
                          kinding_ind e t k -> forall k', k <= k' -> kinding_ind e t k'.
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


(* TODO simplified the equivalences to implications so this plays nice with eauto *)
Lemma bwf_typ_correct : forall t : typ, forall e : env, bwf_typ e t = true -> wf_typ e t.
  induction t.
  - intro. simpl.
    destruct (get_kind e n); [ intuition .. ].
  - intros.
    (* TODO this looks like it could be shorter, but eauto doesn't work *)
    apply andb_true_iff in H.
    split.
    * apply IHt1. apply H.
    * apply IHt2. apply H.
  - intro. apply IHt.
Qed.
    
Lemma bwf_env_correct : forall e : env, bwf_env e = true -> wf_env e.
  induction e.
  - simpl. tauto.
  - intro.
    apply andb_true_iff in H.
    split.
    * apply bwf_typ_correct. apply H.
    * apply IHe. apply H.
  - apply IHe.
Qed.

Theorem kind_of_correct (t : typ) : forall (e : env) (k : kind), kind_of e t = Some k -> kinding_ind e t k.
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

(*
Lemma typing_uniq :
  forall t : term, forall e : env, forall ty1 ty2 : typ,
    typing e t ty1 -> typing e t ty2 -> ty1 = ty2.
  intro.
  induction t.
  - intros. simpl.
    unfold typing in H, H0.
    destruct (get_typ e n).
    + destruct H. destruct H0.
      apply eq_sym in H1.
      apply (eq_trans H2) in H1.
      auto.
    + inversion H.
  - intros.
    destruct ty1.
    + inversion H.
    + simpl in H0.
      destruct ty2.
      * inversion H0.
      * destruct H. destruct H0.
        apply eq_sym in H0. apply (eq_trans H) in H0.
        apply (IHt (evar ty1_1 e) ty1_2 ty2_2) in H1.
        congruence.
        rewrite -> H0.
        apply H2.
      * inversion H0.
    + inversion H.
  - intros.
      destruct H. destruct H0.
      destruct H. destruct H0.
      apply (IHt1 e (tarr x ty1) (tarr x ty2)) in H.
      injection H. trivial.
      apply (IHt2 e x x0) in H1.
      rewrite -> H1. apply H0.
      apply H2.
  - intros.
    simpl in H. simpl in H0.
    destruct ty1.
    + inversion H.
    + inversion H.
    + destruct ty2.
      * inversion H0.
      * inversion H0.
      * destruct H. destruct H0.
        apply (IHt (etvar k e) ty1 ty2) in H1.
        congruence.
        apply H2.
  -  intros.
     simpl in H. simpl in H0.
     do 3 destruct H, H0.
     destruct H1, H2.
     apply (IHt e (tall x x1) (tall x0 x2)) in H.
     injection H. intros.
     rewrite H3. rewrite H4.
     congruence.
     apply H0.
Qed. 

Lemma kind_of_minimal : forall t : typ, forall e : env, forall k : kind,
                          match kind_of e t with
                            | Some k' => kinding e t k -> k' <= k
                            | None => True
                          end.
  induction t.
  - intros.
    simpl.
    remember (bwf_env e) as wfenv.
    remember (get_kind e n) as envkind.
    destruct wfenv.
    + destruct envkind.
      * intros. destruct H. trivial.
      * trivial.
    + trivial.
  - intros.
    simpl.
    specialize (IHt1 e). specialize (IHt2 e).
    remember (kind_of e t1) as kind_t1 in IHt1 |- *.
    remember (kind_of e t2) as kind_t2 in IHt2 |- *.
    destruct kind_t1.
    + destruct kind_t2.
      * intro.
        do 3 destruct H. destruct H0. apply IHt1 in H0. apply IHt2 in H1.
        apply (max_case k0 k1 (fun x => x <= k)).
        assert (x <= max x x0). auto with arith. rewrite -> H in H2. omega.
        assert (x0 <= max x x0). auto with arith. rewrite -> H in H2. omega.
      * trivial.
    + trivial.
  - intros. simpl.
    specialize (IHt (etvar k e)).
    remember (kind_of (etvar k e) t) as kind_e in IHt |- *.
    destruct kind_e.
    + intros. do 2 destruct H.
      apply IHt in H.
      rewrite -> H0.
      apply le_n_S.
      apply (max_case k k1 (fun n => n <= max x k)).
      apply le_max_r.
      assert (x <= max x k). apply le_max_l.
      omega.
    + trivial.
Qed. *)
          
Theorem type_of_correct (t : term) : forall (e : env) (T : typ), type_of e t = Some T -> typing_ind e t T.
  induction t.
  - intros. simpl in H.
    destruct (bwf_env e) eqn:env_is_bwf.
    + auto using t_var, bwf_env_correct.
    + inversion H.
  - intros. simpl in H.
    destruct (type_of (evar t e) t0) eqn:type_of_body.
    + inversion H. auto using t_abs.
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
        { destruct (leq k0 k) eqn:k0_leq_k.
          { inversion H. eapply t_app_t. eauto.
            eauto using kind_of_correct, leq_correct, kinding_ind_sub, t_app_t. }
          { inversion H. } }
        { inversion H. }
    + inversion H.
Qed.