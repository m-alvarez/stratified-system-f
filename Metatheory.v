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
                                  i <= v ->
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
    + inversion H0.
    + simpl. apply (IHe e' i v). simpl in H0. apply H. apply H0. apply H1.
    + inversion H0.
  - intros. destruct e'. 
    + inversion H0.
    + inversion H0.
    + destruct w.
      * destruct i.
        { omega. }
        { destruct H0. rewrite H0. simpl. trivial. }
      * destruct i.
        { omega. }
        { simpl. apply (IHe e' i v). omega. simpl in H0. apply H0. omega. }
Qed.

Lemma insert_kind_get_kind_ge : forall (e e' : env), forall (i v : nat),
                                  i <= v ->
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
    + inversion H0.
    + simpl. apply (IHe e' i v). simpl in H0. apply H. apply H0. apply H1.
    + inversion H0.
  - intros. destruct e'. 
    + inversion H0.
    + inversion H0.
    + destruct w.
      * destruct i.
        { simpl in H0. rewrite H0. simpl. destruct (get_kind e' 0). simpl. trivial. trivial. }
        { omega. }
      * destruct i.
        { simpl in H0. rewrite H0. simpl. destruct (get_kind e' (S w)). trivial. trivial. }
        { simpl. apply (IHe e' i v). omega. simpl in H0. apply H0. omega. }
Qed.
        
Lemma insert_kind_get_kind : forall (e e' : env), forall (v : nat),
                               insert_kind v e e' ->
                               forall (w : nat),
                                 match get_kind e w with
                                   | Some k => get_kind e' (shift_var w v) = Some k
                                   | None => True
                                 end.
  intros.
  unfold shift_var.
  destruct (le_gt_dec v w).
  - apply (insert_kind_get_kind_ge e e' v v). trivial. apply H. omega.
  - apply (insert_kind_get_kind_lt e e' v v). trivial. apply H. omega.
Qed.

Lemma insert_kind_wf_typ : forall (t : typ), forall (e e' : env), forall (v : nat),
                             insert_kind v e e' -> wf_typ e t -> wf_typ e' (tshift v t).
  induction t.
  - intros.
    simpl.
    pose proof (insert_kind_get_kind e e' v H n).
    simpl in H0.
    destruct (get_kind e n).
    + unfold shift_var in H1.
      remember (get_kind e' (if le_gt_dec v n then S n else n)) in H1 |- *.
      destruct o.
      * trivial.
      * inversion H1.
    + inversion H0.
  - intros.
    simpl.
    simpl in H0.
    split.
    { apply (IHt1 e e' v). apply H. apply H0. }
    { apply (IHt2 e e' v). apply H. apply H0. }
  - intros.
    simpl. simpl in H0.
    simpl in H0.
    apply (IHt (etvar k e) (etvar k e') (S v)).
    simpl.
    split.
    trivial.
Qed.

Theorem insert_kind_wf_env : forall (v : nat), forall (e e' : env), insert_kind v e e' -> wf_env e -> wf_env e'.
  intros until e. generalize v. clear v.
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
        apply (insert_kind_wf_typ t e).
        apply H1.
        apply H0.
      * apply (IHe v). apply H. apply H0.
    + inversion H.
  - intros. destruct e'.
    + simpl. trivial.
    + inversion H.
    + destruct v.
      * simpl in H. rewrite <- H. simpl. apply H0.
      * simpl in H. simpl. apply (IHe v e'). apply H. apply H0.
Qed.
  
Theorem insert_kind_kinding : forall (v : nat), forall (e e' : env), forall (t : typ), forall (k : kind),
                                insert_kind v e e' -> kinding e t k -> kinding e' (tshift v t) k.
  intros until t. generalize v, e, e'. clear v. clear e. clear e'.
  induction t.
  - intros.
    simpl. simpl in H0.
    Check insert_kind_get_kind.
    assert ((if le_gt_dec v n then S n else n) = shift_var n v).
    auto.
    rewrite -> H1.
    rewrite <- (insert_kind_get_kind e e' v H).
    remember (get_kind e n) as k1.
    destruct k1.
    + split. apply (insert_kind_wf_env v e e'). apply H. apply H0. apply H0.
    + apply H0.
  - intros. simpl.
    simpl in H0.
    do 2 destruct H0.
    exists x. exists x0.
    split.
    + apply H0.
    + split.
      * apply (IHt1 v e). apply H. apply H0.
      * apply (IHt2 v e). apply H. apply H0.
  - intros. simpl.
    simpl in H0.
    destruct H0.
    exists x.
    split.
    + simpl. apply (IHt (S v) (etvar k e)). simpl. auto. apply H0.
    + apply H0.
Qed.

Lemma insert_kind_get_typ : forall (e e' : env), forall (v : nat),
                              insert_kind v e e' ->
                              forall (w : nat),
                                match get_typ e w with
                                  | Some t => get_typ e' w = Some (tshift v t)
                                  | None => True
                                end.
  induction e.
  - intros.
    simpl.
    trivial.
  - intros.
    destruct e'.
    + inversion H.
    + simpl in H.
      destruct w.
        * simpl. symmetry. destruct H. congruence.
        * simpl. apply IHe. apply H.
    + inversion H.
  - intros.
    destruct e'.
    + inversion H.
    + inversion H.
    + destruct v.
      * simpl in H.
        rewrite <- H.
        remember (get_typ (etvar k e) w).
        destruct o.
        destruct w.
        simpl.
        simpl in Heqo.

Theorem insert_kind_typing : forall (v : nat), forall (e e' : env), forall (t : term), forall (ty : typ),
                               insert_kind v e e' -> typing e t ty -> typing e' t (tshift v ty).
  intros until t. generalize v, e, e'. clear v. clear e. clear e'.
  induction t.
  - intros.
    