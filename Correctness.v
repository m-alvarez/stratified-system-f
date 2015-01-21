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
    simpl in H.
    destruct t2.
    + apply eq_sym in H.
      apply beq_nat_eq in H.
      congruence.
    + inversion H.
    + inversion H.
  - intros.
    simpl in H.
    destruct t2.
    + inversion H.
    + apply andb_true_iff in H.
      destruct H.
      apply IHt1_1 in H.
      apply IHt1_2 in H0.
      congruence.
    + inversion H.
  - intros.
    simpl in H.
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

Theorem leq_prop : forall m n : nat, true = leq m n <-> m <= n.
  induction m.
  - intro. simpl. split. intro. auto with arith. tauto.
  - intro. split.
    + intro. destruct n.
      * simpl in H. inversion H.
      * apply (IHm n) in H. auto with arith.
    + intro. destruct n. exfalso. apply (le_Sn_0 m). apply H. assert (m <= n). omega. apply IHm. apply H0.
Qed.

(* This is actually cumulativity *)
Lemma kinding_sub : forall e : env, forall t : typ, forall k k' : kind,
                       kinding e t k -> k <= k' -> kinding e t k'.
  intro e0. intro t. generalize e0 as e. clear e0. (* This is ugly *)
  induction t.
  - intros.
      simpl.
      simpl in H.
      remember (get_kind e n) as k1 in H |- *.
      destruct k1.
      + split. apply H. destruct H. omega.
      + apply H.
  - intros.
    simpl in H.
    do 3 destruct H. destruct H1.
    simpl.
    exists k'. exists k'.
    split. auto with arith. split.
    apply (IHt1 e x). trivial. assert (x <= max x x0). auto with arith. omega.
    apply (IHt2 e x0). trivial. assert (x0 <= max x x0). auto with arith. omega.
  - intros.
    simpl.
    do 2 destruct H.
    exists (k' - k0 + (max x k)). split.
    apply (IHt (etvar k e) x). apply H.
    assert (x <= max x k). auto with arith. omega.
    assert (max x k >= k). auto with arith. assert (k' - k0 + max x k >= k). omega.
    assert (max (k' - k0 + max x k) k = (k' - k0+ max x k)). auto with arith. rewrite H4.
    rewrite -> H1. assert (S (k' - S (max x k) + max x k) = k' - S (max x k) + S (max x k)).
    rewrite (plus_comm (k' - S (max x k)) (S (max x k))). rewrite le_plus_minus_r. omega.
    omega.
    rewrite -> H5. rewrite (plus_comm). rewrite le_plus_minus_r. trivial.
    rewrite <- H1. apply H0.
Qed.
      
Lemma bwf_typ_correct : forall t : typ, forall e : env, bwf_typ e t = true <-> wf_typ e t.
  induction t.
  - intro.
    simpl.
    remember (get_kind e n) as k in *.
    destruct k.
    + tauto.
    + split.
      * intro. discriminate H.
      * tauto.
  - intro.
    split.
    + intro.
      apply andb_true_iff in H.
      split.
      * apply IHt1. apply H.
      * apply IHt2. apply H.
    + intro.
      apply andb_true_iff.
      split.
      * apply IHt1. apply H.
      * apply IHt2. apply H.
  - intro. apply IHt.
Qed.
    
Lemma bwf_env_correct : forall e : env, bwf_env e = true <-> wf_env e.
  induction e.
  - simpl. tauto.
  - split.
    + intro.
      apply andb_true_iff in H.
      split.
      * apply bwf_typ_correct. apply H.
      * apply IHe. apply H.
    + intro.
      apply andb_true_iff.
      split.
      * apply bwf_typ_correct. apply H.
      * apply IHe. apply H.
  - split; [ apply IHe; apply H .. ].
Qed.

Theorem kind_of_correct : forall t : typ, forall e : env,
                            match kind_of e t with
                              | Some k => kinding e t k
                              | None => forall k : kind, kinding e t k -> False
                            end.
  induction t.
  - intro.
    simpl.
    remember (bwf_env e) as wfe.
    destruct wfe.
    + remember (get_kind e n) as k.
      destruct k.
      * split.
        { apply bwf_env_correct. auto. }
        { auto. }
      * tauto.
    + intro. destruct (get_kind e n).
      * intro.
        destruct H.
        apply bwf_env_correct in H.
        apply (eq_trans Heqwfe) in H.
        discriminate H.
      * tauto.
  - intro.
    simpl.
    specialize (IHt1 e).
    specialize (IHt2 e).
    remember (kind_of e t1) as k in IHt1 |- * .
    destruct k.
    + remember (kind_of e t2) as k2 in IHt2 |- * .
      destruct k2.
      * exists k.
        exists k0.
        split; [ auto .. ].
      * intros.
        do 2 destruct H.
        apply IHt2 with x0.
        apply H.
    + intros.
      do 2 destruct H.
      apply IHt1 with x.
      apply H.
  - intro.
    simpl.
    specialize (IHt (etvar k e)).
    remember (kind_of (etvar k e) t) as k' in IHt |- *.
    destruct k'.
    + exists k0.
      split. apply IHt. rewrite -> max_comm. trivial.
    + intros.
      destruct H.
      apply IHt with (k0 := x).
      apply H.
Qed.

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
Qed.
          
Theorem type_of_correct : forall t : term, forall e : env,
                            match type_of e t with
                              | Some ty => typing e t ty
                              | None => forall ty : typ, typing e t ty -> False
                            end.
  induction t.
  - intro. simpl.
    remember (bwf_env e) as env_bwf.
    + destruct env_bwf.
      * remember (get_typ e n) as t.
        destruct t.
        { split. apply bwf_env_correct. auto. auto. }
        { tauto. }
      * intro.
        destruct (get_typ e n).
        { intro. destruct H. apply bwf_env_correct in H. apply (eq_trans Heqenv_bwf) in H. inversion H. }
        { tauto. }
  - intro. simpl.
    specialize (IHt (evar t e)).
    remember (type_of (evar t e) t0) as ty in IHt |- *.
    destruct ty.
    + split. auto. apply IHt.
    + destruct ty.
      * auto.
      * intro.
        destruct H.
        rewrite -> H in H0.
        apply IHt in H0.
        apply H0.
      * tauto.
  - intro.
    specialize (IHt1 e).
    specialize (IHt2 e).
    simpl.
    remember (type_of e t1) as ty1 in IHt1 |- *.
    remember (type_of e t2) as ty2 in IHt2 |- *.
    destruct ty1.
    + destruct ty2.
      * destruct t.
        { intros. do 2 destruct H.
          apply (typing_uniq t1 e (tvar n) (tarr x ty)) in H.
          discriminate H.
          apply IHt1. }
        { remember (beq_typ t3 t0) as beqt in *.
          destruct beqt.
          { exists t3. split.
            apply IHt1.
            apply eq_sym in Heqbeqt. apply beq_typ_correct in Heqbeqt.
            rewrite -> Heqbeqt. apply IHt2.
          }
          { intros. do 2 destruct H.
            apply (typing_uniq t2 e t0 x) in IHt2.
            apply (typing_uniq t1 e (tarr t3 t4) (tarr x ty)) in IHt1.
            inversion IHt1.
            apply eq_sym in IHt2. apply (eq_trans H2) in IHt2.
            rewrite <- IHt2 in Heqbeqt. 
            pose proof beq_typ_refl as EqRefl.
            specialize (EqRefl t3).
            apply (eq_trans Heqbeqt) in EqRefl. inversion EqRefl.
            apply H.
            apply H0.
          }
        }
        { intros. do 2 destruct H.
          apply (typing_uniq t1 e (tall k t) (tarr x ty)) in IHt1.
          inversion IHt1.
          apply H.
        }
      * destruct t ; [ intros; destruct H; apply (IHt2 x); apply H .. ].
    + intros.
      destruct H.
      apply (IHt1 (tarr x ty)).
      apply H.
  - intros.
    simpl.
    remember (type_of (etvar k e) t) as ty1.
    specialize (IHt (etvar k e)).
    destruct ty1.
    + split.
      * auto.
      * rewrite <- Heqty1 in IHt.
        apply IHt.
    + rewrite <- Heqty1 in IHt.
      intro.
      destruct ty.
      * auto.
      * auto.
      * intro. apply (IHt ty). apply H.
  - intros.
    simpl.   
    specialize (IHt e).
    remember (type_of e t) as ty in IHt |- *.
    destruct ty.
    destruct t1.
    + intros. do 2 destruct H.
      apply (typing_uniq t e (tvar n) (tall x x0)) in IHt.
      inversion IHt.
      apply H.
    + intros. do 2 destruct H. 
      apply (typing_uniq t e (tarr t1_1 t1_2) (tall x x0)) in IHt.
      inversion IHt.
      apply H.
    + remember (kind_of e t0) as k0 in *.
      destruct k0.
      remember (leq k0 k) as lk0.
      destruct lk0.
      * exists k, t1. split. apply IHt. split.
        pose proof (kind_of_correct t0 e).
        rewrite <- Heqk0 in H.
        apply (kinding_sub e t0 k0 k).
        apply H.
        apply leq_prop.
        apply Heqlk0.
        trivial.
      * intros.
        do 3 destruct H. destruct H0.
        pose proof kind_of_minimal.
        specialize (H2 t0 e x).
        rewrite <- Heqk0 in H2.
        apply H2 in H0.
        pose proof (typing_uniq t e (tall k t1) (tall x x0) IHt H).
        inversion H3.
        pose proof (leq_prop k0 k).
        destruct H4.
        rewrite <- H5 in H0. apply H7 in H0. apply eq_sym in H0. apply (eq_trans Heqlk0) in H0.
        discriminate H0.
      * intros.
        do 3 destruct H. destruct H0.
        pose proof (kind_of_correct t0 e).
        rewrite <- Heqk0 in H2. apply H2 in H0. apply H0.
    + intros. do 3 destruct H. apply (IHt (tall x x0)). apply H.
Qed.