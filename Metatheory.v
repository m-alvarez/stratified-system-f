Add LoadPath ".".

Require Import SysF.
Require Import Arith.
Require Import Omega.

Lemma cumulativity : forall e : env, forall t : typ, forall k k' : kind,
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

Fixpoint insert_kind_r (i : nat) (v : nat) (e : env) (e' : env) : Prop :=
  match e with
    | evar t e1 =>
      match e' with
        | evar t' e1' => (tshift v t) = t' /\ insert_kind_r i v e1 e1'
        | _ => False
      end
    | etvar k e1 =>
      match e' with
        | etvar k' e1' =>
          match i with
            | 0 => etvar k e1 = e1'
            | S i1 => k = k' /\ insert_kind_r i1 v e1 e1'
          end
        | _ => False
      end
    | empty =>
      match e' with
        | etvar k empty => v = 0
        | _ => False
      end
  end.

Definition insert_kind (v : nat) := insert_kind_r v v.

Hint Transparent insert_kind : core.
Hint Transparent insert_kind_r : core.
Hint Unfold insert_kind : core.
Hint Unfold insert_kind_r : core.

Definition shift_var (v : nat) (i : nat) :=
  if le_gt_dec i v
  then S v
  else v.

Lemma shift_var_s : forall (v i : nat), shift_var (S v) (S i) = S (shift_var v i).
  induction v.
  - destruct i; [ simpl; compute; trivial .. ].
  - destruct i.
    + compute. trivial.
    + specialize (IHv i).
      unfold shift_var in IHv |- *.
      remember (le_gt_dec (S i) (S v)).
      remember (le_gt_dec (S (S i)) (S (S v))).
      destruct s.
      * destruct s0.
        { reflexivity. }
        { exfalso. omega. }
      * destruct s0.
        { exfalso. omega. }
        { reflexivity. }
Qed.

Lemma insert_kind_get_kind_lt : forall (e e' : env), forall (i v : nat),
                                  insert_kind_r i v e e' ->
                                  forall (w : nat),
                                    w < i ->
                                    match get_kind e w with
                                      | Some k => get_kind e' w = Some k
                                      | None => True
                                    end.
  induction e.
  - intros. simpl. trivial.
  - intros. simpl. destruct e'.
    + inversion H.
    + simpl. apply (IHe e' i v). simpl in H. apply H. apply H0.
    + inversion H.
  - intros. destruct e'. 
    + inversion H.
    + inversion H.
    + destruct w.
      * destruct i.
        { omega. }
        { destruct H. rewrite H. simpl. trivial. }
      * destruct i.
        { omega. }
        { simpl. apply (IHe e' i v). apply H. omega. }
Qed.

Lemma insert_kind_get_kind_ge : forall (e e' : env), forall (i v : nat),
                                  insert_kind_r i v e e' ->
                                  forall (w : nat),
                                    w >= i ->
                                    match get_kind e w with
                                      | Some k => get_kind e' (S w) = Some k
                                      | None => True
                                    end.
  induction e.
  - intros. simpl. trivial.
  - intros. simpl. destruct e'.
    + inversion H.
    + simpl. apply (IHe e' i v). simpl in H. apply H. apply H0.
    + inversion H.
  - intros. destruct e'. 
    + inversion H.
    + inversion H.
    + destruct w.
      * destruct i.
        { simpl in H. rewrite H. simpl. destruct (get_kind e' 0). simpl. trivial. trivial. }
        { omega. }
      * destruct i.
        { simpl in H. rewrite H. simpl. destruct (get_kind e' (S w)). trivial. trivial. }
        { simpl. apply (IHe e' i v). apply H. omega. }
Qed.
        
Lemma insert_kind_get_kind : forall (e e' : env), forall (i v : nat),
                               insert_kind_r i v e e' ->
                               forall (w : nat),
                                 match get_kind e w with
                                   | Some k => get_kind e' (shift_var w i) = Some k
                                   | None => True
                                 end.
  intros.
  unfold shift_var.
  destruct (le_gt_dec i w).
  - apply (insert_kind_get_kind_ge e e' i v H w l).
  - apply (insert_kind_get_kind_lt e e' i v H w g).
Qed.

Definition exists_kind (e : env) (n : nat) := match get_kind e n with Some _ => True | None => False end.
Hint Transparent exists_kind : core.
Hint Unfold exists_kind : core.

Fixpoint highest_free_typ_variable (t : typ) :=
  match t with
    | tvar n => Some n
    | tarr t1 t2 => match highest_free_typ_variable t1 with
                      | None => highest_free_typ_variable t2
                      | Some h1 => match highest_free_typ_variable t2 with
                                     | None => Some h1
                                     | Some h2 => if le_gt_dec h1 h2 then Some h2 else Some h1
                                   end
                    end
    | tall _ t1 => match highest_free_typ_variable t1 with
                     | None => None
                     | Some 0 => None
                     | Some (S n) => Some n
                   end
  end.

Fixpoint num_typ_variables (e : env) :=
  match e with
    | empty => 0
    | etvar _ e' => S (num_typ_variables e')
    | evar _ e => num_typ_variables e
  end.

Lemma get_free_variable : forall e, forall n,
                            n < num_typ_variables e <-> exists_kind e n.
  induction e.
  - simpl. intros. split. omega. intro. inversion H.
  - intros. split.
    + intro. simpl in H |- *. apply IHe. apply H.
    + unfold exists_kind. simpl. apply IHe.
  - intros. split.
    + intro. unfold exists_kind.  simpl in H.
      destruct n.
      * simpl. trivial.
      * apply IHe. auto with arith.
    + intro. destruct n.
      * simpl. auto with arith.
      * simpl in H |- *. apply lt_n_S. apply IHe. apply H.
Qed.

Lemma num_typ_variables_significant : forall (t : typ), forall (e : env),
                                        wf_typ e t <->
                                        match highest_free_typ_variable t with
                                          | None => True
                                          | Some i => i < num_typ_variables e
                                        end.
  split. generalize e. clear e. {
  induction t.
  - intros. simpl. apply get_free_variable. apply H.
  - intros. simpl. destruct (highest_free_typ_variable t1); destruct (highest_free_typ_variable t2).
    + destruct (le_gt_dec n n0).
      * apply IHt2. apply H.
      * apply IHt1. apply H.
    + apply IHt1. apply H.
    + apply IHt2. apply H.
    + trivial.
  - intros. simpl in H.
    simpl. remember (highest_free_typ_variable t). destruct (highest_free_typ_variable t).
    + rewrite Heqo in IHt |- *. destruct n.
      * trivial.
      * assert (S n < num_typ_variables (etvar k e) -> n < num_typ_variables e). simpl. auto with arith.
        apply H0. apply (IHt (etvar k e) H).
    + rewrite -> Heqo. trivial.
  } 
                                generalize e. clear e. induction t.
  - intros. apply get_free_variable. apply H.
  - intros. simpl in H. destruct (highest_free_typ_variable t1); destruct (highest_free_typ_variable t2).
    + destruct (le_gt_dec n n0). 
      * split. { apply IHt1. omega. } { apply IHt2. omega. }
      * split. { apply IHt1. omega. } { apply IHt2. omega. } 
    + split. { apply IHt1, H. } { apply IHt2. trivial. }
    + split. { apply IHt1. trivial. } { apply IHt2, H. }
    + split. { apply IHt1. trivial. } { apply IHt2. trivial. }
  - intros. simpl. apply IHt. remember (highest_free_typ_variable (tall k t)) in H.
    destruct o. simpl in Heqo.
    destruct (highest_free_typ_variable t).
    + destruct n0. inversion Heqo. simpl. apply lt_n_S. inversion Heqo. rewrite <- H1. apply H.
    + trivial.
    + simpl. simpl in Heqo. destruct (highest_free_typ_variable t). 
      * destruct n. auto with arith. inversion Heqo.
      * trivial.
Qed.

Lemma num_typ_variables_insert_kind : forall e e' i n,
                                        insert_kind_r i n e e'
                                        -> num_typ_variables e' = S (num_typ_variables e).
  unfold insert_kind.
  induction e.
  - intros. destruct e'. inversion H. inversion H.
    + destruct e'. trivial. inversion H. inversion H.
  - intros. destruct e'. 
    + inversion H.
    + simpl in H. apply (IHe e' i n). apply H. 
    + inversion H.
  - intros. destruct e'. inversion H. inversion H.
    destruct i.
    + simpl in H. rewrite <- H. simpl. trivial.
    + simpl. simpl in H. specialize (IHe e' i n).
      assert (num_typ_variables e' = S (num_typ_variables e)). apply IHe. apply H. congruence.
Qed.

Lemma highest_free_typ_variable_tshift_s
: forall t v, match highest_free_typ_variable (tshift (S v) t) with
                | Some n1 =>
                  match highest_free_typ_variable (tshift v t) with
                    | None => n1 = 0
                    | Some n2 => n1 <= S n2
                  end
                | None => True
              end.
  induction t.
  - intros. unfold tshift. destruct (le_gt_dec v n); destruct (le_gt_dec (S v) n).
    + simpl. auto with arith. + simpl. auto with arith. + simpl. trivial. + simpl. auto with arith.
  - intros. specialize (IHt1 v). specialize (IHt2 v).
    simpl. destruct (highest_free_typ_variable (tshift (S v) t1));
      destruct (highest_free_typ_variable (tshift (S v) t2)).
    + destruct (highest_free_typ_variable (tshift (v) t1));
      destruct (highest_free_typ_variable (tshift (v) t2)).
      destruct (le_gt_dec n n0); destruct (le_gt_dec n1 n2). 
      omega. omega. omega. omega. destruct (le_gt_dec n n0). omega. omega.
      destruct (le_gt_dec n n0). omega. omega. destruct (le_gt_dec n n0). omega. omega.
    + destruct (highest_free_typ_variable (tshift v t1)).
      destruct (highest_free_typ_variable (tshift v t2)).
      destruct (le_gt_dec n0 n1). omega. omega. omega.
      destruct (highest_free_typ_variable (tshift v t2)).
      omega. omega.
    + destruct (highest_free_typ_variable (tshift v t2)).
      destruct (highest_free_typ_variable (tshift v t1)).
      destruct (le_gt_dec n1 n0). omega. omega. omega.
      destruct (highest_free_typ_variable (tshift v t1)).
      omega. omega.
    + trivial.
  - intros. simpl. specialize (IHt (S v)).
    destruct (highest_free_typ_variable (tshift (S v) t)).
    + destruct (highest_free_typ_variable (tshift (S (S v)) t)).
      * destruct n.
        { destruct n0. trivial. omega. }
        { destruct n0. trivial. omega. }
      * trivial.
    + destruct (highest_free_typ_variable (tshift (S (S v)) t)).
      * destruct n. trivial. inversion IHt.
      * trivial.
Qed.

Lemma highest_free_variable_tshift
: forall t v, match highest_free_typ_variable t with
                | None =>
                  match highest_free_typ_variable (tshift v t) with
                    | None => True
                    | Some 0 => True
                    | _ => False
                  end
                | Some t1 =>
                    match highest_free_typ_variable (tshift v t) with
                      | Some t2 => t2 <= S t1
                      | None => True
                    end
              end.
  induction t.
  - intros. unfold tshift. destruct (le_gt_dec v n).
    + simpl. trivial.
    + simpl. auto with arith.
  - intros. specialize (IHt1 v). specialize (IHt2 v).
    simpl. destruct (highest_free_typ_variable t1); destruct (highest_free_typ_variable t2).
    + destruct (le_gt_dec n n0).
      * destruct (highest_free_typ_variable (tshift v t1));
        destruct (highest_free_typ_variable (tshift v t2)).
        destruct (le_gt_dec n1 n2).
        { omega. } { omega. } { omega. } { omega. } { trivial. }
      * destruct (highest_free_typ_variable (tshift v t1));
        destruct (highest_free_typ_variable (tshift v t2)).
        destruct (le_gt_dec n1 n2).
        { omega. } { omega. } { omega. } { omega. } { trivial. }
    + destruct (highest_free_typ_variable (tshift v t1));
      destruct (highest_free_typ_variable (tshift v t2)).
      destruct (le_gt_dec n0 n1). destruct n1. omega. omega. omega. omega.
      destruct n0; [trivial | auto]. omega. omega. trivial.
    + destruct (highest_free_typ_variable (tshift v t1));
      destruct (highest_free_typ_variable (tshift v t2)).
      destruct (le_gt_dec n0 n1). destruct n1. omega. omega.
      destruct n0. omega. omega. destruct n0. omega. omega. omega. trivial.
    + destruct (highest_free_typ_variable (tshift v t1));
      destruct (highest_free_typ_variable (tshift v t2)).
      destruct (le_gt_dec n n0). apply IHt2. apply IHt1. apply IHt1. apply IHt2. trivial.
  - intros. simpl. pose proof (highest_free_typ_variable_tshift_s t v).
    destruct (highest_free_typ_variable t). 
    + specialize (IHt (S v)). destruct n.
      * destruct (highest_free_typ_variable (tshift (S v) t)).
        destruct n. trivial. destruct n. trivial. omega. trivial.
      * destruct (highest_free_typ_variable (tshift (S v) t)).
        destruct n0. trivial. destruct (highest_free_typ_variable (tshift v t)). omega. omega. trivial.
    + specialize (IHt (S v)). destruct (highest_free_typ_variable (tshift (S v) t)). destruct n.
      * trivial. * inversion IHt. * trivial.
Qed.
                                   
Lemma insert_kind_wf_typ : forall (t : typ), forall (e e' : env), forall (i v : nat),
                             insert_kind_r i v e e' ->
                             wf_typ e t -> wf_typ e' (tshift v t).
  intros.
  pose proof (highest_free_variable_tshift t v).
  pose proof (num_typ_variables_insert_kind e e' i v H).
  pose proof (num_typ_variables_significant (tshift v t) e').
  pose proof (num_typ_variables_significant t e).
  rewrite H2 in H3. destruct H3. apply H5.
  apply num_typ_variables_significant in H5.
  - destruct (highest_free_typ_variable (tshift v t)).
    + destruct (highest_free_typ_variable t).
      * omega. * omega.
    + trivial.
  - destruct (highest_free_typ_variable (tshift v t)).
    + destruct (highest_free_typ_variable t).
      apply H4 in H0. omega. destruct n. omega. inversion H1.
    + trivial.
Qed.

Theorem insert_kind_wf_env_r :
  forall (i v : nat), forall (e e' : env), insert_kind_r i v e e' -> wf_env e -> wf_env e'.
  intros until e. generalize i, v. clear i. clear v.
  induction e.
  - intros. destruct e'.
    + inversion H.
    + inversion H.
    + simpl in H. destruct e'.
      * trivial.
      * inversion H.
      * inversion H.
  - intros. destruct e'.
    + simpl. trivial.
    + simpl. split. 
      * simpl in H.
        simpl in H0.
        destruct H.
        rewrite <- H.
        apply (insert_kind_wf_typ t e e' i v H1).
        apply H0.
      * apply (IHe i v). apply H. apply H0.
    + inversion H.
  - intros. destruct e'.
    + simpl. trivial.
    + inversion H.
    + destruct i.
      * simpl in H. rewrite <- H. simpl. apply H0.
      * simpl in H. simpl. apply (IHe i v e'). apply H. apply H0.
Qed.

Theorem insert_kind_wf_env : forall v, forall e e', insert_kind v e e' -> wf_env e -> wf_env e'.
  intros.
  apply (insert_kind_wf_env_r v v e e'); [auto..].
Qed.

Theorem insert_kind_kinding_r : forall (i v : nat), forall (e e' : env), forall (t : typ), forall (k : kind),
                                  insert_kind_r i v e e' -> kinding e t k -> kinding e' (tshift i t) k.
  intros until t. generalize i, v, e, e'. clear i. clear v. clear e. clear e'.
  induction t.
  - intros.
    simpl. simpl in H0.
    assert ((if le_gt_dec i n then S n else n) = shift_var n i). auto.
    rewrite -> H1.
    pose proof (insert_kind_get_kind e e' i v H n). 
    destruct (get_kind e n).
    + rewrite -> H2.
      split.
      * apply (insert_kind_wf_env_r i v e e'). auto. apply H0.
      * apply H0.
    + inversion H0.
  - intros. simpl.
    do 2 destruct H0.
    exists x. exists x0.
    split.
    + apply H0.
    + split.
      * apply (IHt1 i v e). apply H. apply H0.
      * apply (IHt2 i v e). apply H. apply H0.
  - intros. simpl.
    destruct H0.
    exists x.
    split.
    + apply (IHt (S i) v (etvar k e)). simpl. split. trivial. apply H. apply H0.
    + apply H0.
Qed.

Theorem insert_kind_get_typ_r : forall (e e' : env), forall (i v : nat), forall (n : nat),
                                  insert_kind_r i v e e' ->
                                  match get_typ e n with
                                    | Some t => get_typ e' (shift_var i n) = Some (tshift v t)
                                    | None => True
                                  end.
  induction e.
  - intros. simpl. trivial.
  - intros. destruct e'. inversion H.
    + specialize (IHe e' i v n). destruct H.