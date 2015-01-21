Require Import Arith.
Require Import Arith.Max.
Require Import Omega.
Require Import Lt.
Require Import Bool.

Add LoadPath ".".

Require Import SysF.

Lemma beq_typ_correct : forall t1 t2 : typ, beq_typ t1 t2 = true -> t1 = t2.
  intro.
  induction t1.
  + {
      intros.
      simpl in H.
      destruct t2.
      - {
          apply eq_sym in H.
          apply beq_nat_eq in H.
          congruence.
        }
      - inversion H.
      - inversion H.
    }
  + {
      intros.
      simpl in H.
      destruct t2.
      - inversion H.
      - {
          apply andb_true_iff in H.
          destruct H.
          apply IHt1_1 in H.
          apply IHt1_2 in H0.
          congruence.
        }
      - inversion H.
    }
  + {
      intros.
      simpl in H.
      destruct t2.
      - inversion H.
      - inversion H.
      - {
          apply andb_true_iff in H.
          destruct H.
          apply IHt1 in H0.
          apply eq_sym in H. apply beq_nat_eq in H.
          congruence.
        }
    }
Qed.

Lemma beq_typ_refl : forall t : typ, beq_typ t t = true.
  intro.
  induction t.
  + simpl. apply eq_sym. apply beq_nat_refl.
  + simpl. apply andb_true_iff. split. apply IHt1. apply IHt2.
  + simpl. apply andb_true_iff. split. apply eq_sym. apply beq_nat_refl. apply IHt.
Qed.

Theorem leq_prop : forall m n : nat, true = leq m n <-> m <= n.
  intro.
  induction m.
  intro. simpl. split. intro. auto with arith. tauto.
  intro. split.
  intro. destruct n. simpl in H. inversion H. specialize (IHm n). simpl in H. apply IHm in H.
  auto with arith.
  intro.
  simpl. destruct n. exfalso. apply (le_Sn_0 m). apply H.
  assert (m <= n). omega. apply IHm. apply H0.
Qed.

(* This is actually cumulativity *)
Lemma kinding_sub : forall t : typ, forall e : env, forall k1 k2 : kind,
                      k1 <= k2 -> kinding e t k1 -> kinding e t k2.
  intro.
  induction t.
  + {
      intros.
      simpl.
      simpl in H0.
      remember (get_kind e n) as k' in H0 |- *.
      destruct k'.
      - split. apply H0. destruct H0. omega.
      - apply H0.
    }
  + {
      intros.
      simpl.
      simpl in H0.
      destruct H0. destruct H0.
      specialize (IHt1 e x).
      specialize (IHt2 e x0).
      exists k2. exists k2.
      destruct H0. destruct H0. destruct H1.
      split. apply max_l. trivial.
      split. apply IHt1. assert (x <= max x x0). auto with arith. omega. apply H0.
      apply IHt2. assert (x0 <= max x x0). auto with arith. omega. apply H1.
    }
  + {
      intros.
      simpl.
      simpl in H0. destruct H0. destruct H0.
      exists (k2 - k1 + (max x k)). split.
      apply (IHt (etvar k e) x). assert (x <= max x k). auto with arith. omega. apply H0.
      assert (max x k >= k). auto with arith. assert (k2 - k1 + max x k >= k). omega.
      assert (max (k2 - k1 + max x k) k = (k2 - k1 + max x k)). auto with arith. rewrite H4.
      rewrite -> H1. assert (S (k2 - S (max x k) + max x k) = k2 - S (max x k) + S (max x k)).
      omega. rewrite -> H5. assert (k2 - S (max x k) + S (max x k) = k2 - (S (max x k) - S (max x k))).
      omega. (* THIS TAKES A WHILE *) rewrite H6. rewrite (minus_diag (S (max x k))). auto with arith.
    }
Qed.
      
Theorem kind_of_correct : forall t : typ, forall e : env,
                            match kind_of e t with
                              | Some k => kinding e t k
                              | None => forall k : kind, kinding e t k -> False
                            end.
  intro.
  induction t.
  + { (* tvar *)
      intro.
      simpl.
      unfold wf_env.
      case (bwf_env e).
      - {
          case (get_kind e n).
          auto.
          auto.
        }
      - {
          case (get_kind e n).
          intros. destruct H. discriminate H. auto.
        }
    }
  + { (* tarr *)
      intro.
      simpl.
      specialize (IHt1 e).
      specialize (IHt2 e).
      remember (kind_of e t1) as k in IHt1 |- *.
      destruct k.
      - (* some k *) {
         remember (kind_of e t2) as k2 in IHt2 |- *.
          destruct k2.
          * {
              exists k.
              exists k0.
              split.
              auto. auto.
            }
          * {
              intros.
              destruct H.
              destruct H.
              apply IHt2 with x0.
              destruct H.
              destruct H0.
              apply H1.
            }
        }
      - (* none *) {
          intros.
          destruct H.
          destruct H.
          apply IHt1 with x.
          destruct H.
          destruct H0.
          apply H0.
        }
    }
  + (* tall *) {
      intro.
      simpl.
      specialize (IHt (etvar k e)).
      remember (kind_of (etvar k e) t) as k' in IHt |- *.
      destruct k'.
      * {
          exists k0.
          split. apply IHt. rewrite -> max_comm. trivial.
        }
      * {
          intro.
          intro.
          destruct H.
          apply IHt with (k0 := x).
          destruct H.
          apply H.
        }
    }
Qed.

Lemma typing_uniq :
  forall t : term, forall e : env, forall ty1 ty2 : typ,
    typing e t ty1 -> typing e t ty2 -> ty1 = ty2.
  intro.
  induction t.
  + {
      intros. simpl.
      unfold typing in H.
      unfold typing in H0.
      destruct (get_typ e n).
      destruct H. destruct H0.
      apply eq_sym in H1.
      apply (eq_trans H2) in H1.
      auto.
      inversion H.
    }
  + {
      intros.
      simpl in H.
      destruct ty1.
      - inversion H.
      - {
          simpl in H0.
          destruct ty2.
          * inversion H0.
          * {
              destruct H. destruct H0.
              apply eq_sym in H0. apply (eq_trans H) in H0.
              apply (IHt (evar ty1_1 e) ty1_2 ty2_2) in H1.
              congruence.
              rewrite -> H0.
              apply H2.
            }
          * inversion H0.
        }
      - inversion H.
    }
  + {
      intros.
      simpl in H. simpl in H0.
      destruct H. destruct H0.
      destruct H. destruct H0.
      apply (IHt1 e (tarr x ty1) (tarr x ty2)) in H.
      injection H. trivial.
      apply (IHt2 e x x0) in H1.
      rewrite -> H1. apply H0.
      apply H2.
    }
  + {
      intros.
      simpl in H. simpl in H0.
      destruct ty1.
      - inversion H.
      - inversion H.
      - destruct ty2.
        * inversion H0.
        * inversion H0.
        * {
            destruct H. destruct H0.
            apply (IHt (etvar k e) ty1 ty2) in H1.
            congruence.
            apply H2.
          }
    }
  + {
      intros.
      simpl in H. simpl in H0.
      destruct H. destruct H0.
      destruct H. destruct H0.
      destruct H. destruct H0. destruct H1. destruct H2.
      apply (IHt e (tall x x1) (tall x0 x2)) in H.
      injection H. intros.
      rewrite H3. rewrite H4.
      congruence.
      apply H0.
    }
Qed.

Lemma kind_of_minimal : forall t : typ, forall e : env, forall k : kind,
                          match kind_of e t with
                            | Some k' => kinding e t k -> k' <= k
                            | None => kinding e t k -> False
                          end.
  intro. induction t.
  + {
      intros. simpl.
      remember (bwf_env e) as wfenv.
      remember (get_kind e n) as envkind.
      destruct wfenv.
      - {
          destruct envkind.
          * intros. destruct H. trivial.
          * trivial.
        }
      - {
          intros.
          destruct envkind.
          * destruct H. unfold wf_env in H. apply (eq_trans Heqwfenv) in H. inversion H.
          * apply H.
        }
    }
  + {
      intros.
      simpl.
      specialize (IHt1 e). specialize (IHt2 e).
      remember (kind_of e t1) as kind_t1 in IHt1 |- *.
      remember (kind_of e t2) as kind_t2 in IHt2 |- *.
      destruct kind_t1.
      - {
          destruct kind_t2.
          * {
              intro.
              destruct H. destruct H. destruct H. destruct H0. apply IHt1 in H0. apply IHt2 in H1.
              apply (max_case k0 k1 (fun x => x <= k)).
              assert (x <= max x x0). auto with arith. rewrite -> H in H2. omega.
              assert (x0 <= max x x0). auto with arith. rewrite -> H in H2. omega.
            }
          * intros. destruct H. destruct H. destruct H. destruct H0. apply (IHt2 x0). apply H1.
        }
      - intros. destruct H. destruct H. destruct H. destruct H0. apply (IHt1 x). apply H0.
    }
  + {
      intros. simpl.
      specialize (IHt (etvar k e)).
      remember (kind_of (etvar k e) t) as kind_e in IHt |- *.
      destruct kind_e.
      - {
          intros. destruct H. destruct H.
          apply IHt in H.
          rewrite -> H0.
          apply le_n_S.
          apply (max_case k k1 (fun n => n <= max x k)).
          apply le_max_r.
          assert (x <= max x k). apply le_max_l.
          omega.
        }
      - intros. destruct H. destruct H. apply (IHt x). apply H.
    }
Qed.
          
Theorem type_of_correct : forall t : term, forall e : env,
                            match type_of e t with
                              | Some ty => typing e t ty
                              | None => forall ty : typ, typing e t ty -> False
                            end.
  intro.
  induction t.
  + (* var *) {
      intro. simpl.
      case (get_typ e n).
      - {
          intro. unfold wf_env. case (bwf_env e).
          auto.
          intros. destruct H. discriminate H.
        }
      - case (bwf_env e). auto. auto.
    }
  + (* abs *) {
      intro.
      simpl.
      specialize (IHt (evar t e)).
      remember (type_of (evar t e) t0) as ty in IHt |- *.
      destruct ty.
      - split. auto. apply IHt.
      - {
          intro.
          destruct ty.
          * auto.
          * {
              intro.
              destruct H.
              apply IHt with (ty := ty2).
              rewrite <- H.
              apply H0.
            }
          * auto.
        }
    }
  + (* app *) {
      intro.
      specialize (IHt1 e).
      specialize (IHt2 e).
      simpl.
      remember (type_of e t1) as ty1 in IHt1 |- *.
      remember (type_of e t2) as ty2 in IHt2 |- *.
      destruct ty1.
      destruct ty2.
      - {
          destruct t.
          * {
              intros.
              destruct H. destruct H.
              Check typing_uniq.
              apply (typing_uniq t1 e (tvar n) (tarr x ty)) in IHt1.
              discriminate IHt1.
              apply H.
            }
          * {
              remember (beq_typ t3 t0) as beqt in *.
              destruct beqt.
              - {
                  exists t3.
                  split.
                  apply IHt1.
                  apply eq_sym in Heqbeqt. apply beq_typ_correct in Heqbeqt.
                  rewrite -> Heqbeqt. apply IHt2.
                }
              - {
                  intros.
                  destruct H.
                  destruct H.
                  Check typing_uniq.
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
          * {
              intros.
              destruct H. destruct H.
              apply (typing_uniq t1 e (tall k t) (tarr x ty)) in IHt1.
              inversion IHt1.
              apply H.
            }
        }
      - {
          destruct t.
          * intros. destruct H. apply (IHt2 x). apply H.
          * intros. destruct H. apply (IHt2 x). apply H.
          * intros. destruct H. apply (IHt2 x). apply H.
        }
      - {
          intros.
          destruct H.
          apply (IHt1 (tarr x ty)).
          apply H.
        }
    }
  + (* abs_t *) {
      intros.
      simpl.
      remember (type_of (etvar k e) t) as ty1.
      specialize (IHt (etvar k e)).
      destruct ty1.
      - {
          split. auto.
          rewrite <- Heqty1 in IHt.
          apply IHt.
        }
      - {
          rewrite <- Heqty1 in IHt.
          intro. destruct ty.
          auto.
          auto.
          intro.
          apply (IHt ty).
          apply H.
        }
    }
  + (* app_t *) {
      intros.
      simpl.   
      specialize (IHt e).
      remember (type_of e t) as ty in IHt |- *.
      destruct ty.
      destruct t1.
      - {
          intros.
          destruct H. destruct H. destruct H.
          apply (typing_uniq t e (tvar n) (tall x x0)) in IHt. inversion IHt. apply H.
        }
      - {
          intros. destruct H. destruct H. destruct H.
          apply (typing_uniq t e (tarr t1_1 t1_2) (tall x x0)) in IHt. inversion IHt. apply H.
        }
      - {
          remember (kind_of e t0) as k0 in *.
          destruct k0.
          remember (leq k0 k) as lk0.
          destruct lk0.
          * {
              exists k. exists t1. split. apply IHt. split.
              pose proof (kind_of_correct t0 e). rewrite <- Heqk0 in H.
              apply (kinding_sub t0 e k0 k).
              apply leq_prop. apply Heqlk0.
              apply H.
              reflexivity.
            }
          * {
              intros.
              destruct H. destruct H. destruct H. destruct H0.
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
            }
          * {
              intros.
              destruct H. destruct H. destruct H. destruct H0.
              Check kind_of_correct.
              pose proof (kind_of_correct t0 e).
              rewrite <- Heqk0 in H2. apply H2 in H0. apply H0.
            }
        }
      - intros. destruct H. destruct H. destruct H. apply (IHt (tall x x0)). apply H.
    }
Qed.