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

Fixpoint insert_kind (v : nat) (e : env) (e' : env) : Prop :=
  match (e, e') with
    | (evar t e1, evar t' e1') => (tshift v t) = t' /\ insert_kind v e1 e1'
    | (etvar k e1, etvar k' e1') =>
      match v with
        | 0 => etvar k e1 = e1'
        | S v1 => k = k' /\ insert_kind v1 e1 e1'
      end
    | (empty, etvar k empty) => v = 0
    | _ => False
  end.

Lemma get_kind_Sv : forall (v : nat), forall e : env, get_kind e (S v) <> None -> get_kind e v <> None.
  intros until e. generalize v. induction e.
  - intros. simpl in H. simpl. apply H.
  - intros. simpl. simpl in H. apply (IHe v0). apply H.
  - intros. destruct v0.
    + simpl. intro. inversion H0.
    + simpl. simpl in H.  apply IHe. apply H.
Qed.

Lemma get_kind_etvar : forall e : env, forall v : nat, get_kind e v <> None ->
                                                       forall k : kind, get_kind (etvar k e) v <> None.
  intro. induction e.
  - intros. destruct v; [ simpl in H; exfalso; apply H; reflexivity .. ].
  - intros. destruct v.
    + simpl. intro. inversion H0.
    + simpl. simpl in H. apply get_kind_Sv. apply H.
  - intros. destruct v.
    + simpl. intro. inversion H0.
    + simpl. destruct v.
      * simpl. intro. inversion H0.
      * simpl. simpl in H. apply get_kind_Sv. apply H.
Qed.

Lemma get_kind_evar : forall e : env, forall v : nat, get_kind e v <> None ->
                                                      forall t : typ, get_kind (evar t e) v <> None.
  intro. induction e.
  - intros. destruct v; [ simpl in H; exfalso; apply H; reflexivity .. ].
  - intros. simpl in H. simpl. apply H.
  - intros. simpl. apply H.
Qed.

Definition fix_var (v : nat) (i : nat) :=
  if le_gt_dec i v
  then S v
  else v.

Lemma get_kind_fix_var : forall (v i : nat), forall (e : env),
                          get_kind e v <> None -> get_kind e (S v) <> None ->
                          get_kind e (fix_var v i) <> None.
  intros.
  unfold fix_var.
  destruct (le_gt_dec i v).
  - auto.
  - auto.
Qed.

Lemma get_kind_Sn : forall (e : env), forall (v : nat), get_kind e (S v) <> None -> get_kind e v <> None.
  induction e.
  - intros. exfalso. apply H. trivial.
  - intros. apply IHe. apply H.
  - intros. destruct v; [ intro; inversion H0 | apply IHe; apply H ].
Qed.

Lemma insert_kind_get_kind_etvar : forall (e e' : env), forall (v : nat),
                                  insert_kind v e e' ->
                                  forall (w : nat), forall (k : kind),
                                    get_kind (etvar k e) w <> None -> get_kind e' w <> None.
  induction e.
  - intros. destruct e'.
    + inversion H.
    + inversion H.
    + destruct w.
      { simpl. intro. inversion H1. }
      { simpl. simpl H. destruct e'.
        * simpl. auto.
        * simpl in H. auto.
        * inversion H. }
  - intros. destruct e'.
    + inversion H.
    + simpl in H. simpl. apply (fun h => IHe e' v h w k). apply H.
      destruct w.
      * simpl. auto.
      * apply H0.
    + inversion H.
  - intros. destruct e'.
    + inversion H.
    + inversion H.
    + destruct w.
      * simpl. intro. inversion H1.
      * destruct v.
        { simpl in H. rewrite <- H. apply H0. }
        { simpl. simpl in H. apply (fun h => IHe e' v h w k). apply H. apply H0. }
Qed.

Lemma insert_kind_get_kind_Sn : forall (e e' : env), forall (v : nat),
                                  insert_kind v e e' -> forall (w : nat), get_kind e w <> None -> get_kind e' (S w) <> None.
  intros.
  apply (insert_kind_get_kind_etvar e e' v H (S w) 0).
  apply H0.
Qed.

Lemma insert_kind_get_kind_n : forall (e e' : env), forall (v : nat),
                                 insert_kind v e e' -> forall (w : nat), get_kind e w <> None -> get_kind e' w <> None.
  intros.
  apply (insert_kind_get_kind_etvar e e' v H w 0).
  apply get_kind_etvar.
  auto.
Qed.

Lemma fix_var_s : forall (v i : nat), fix_var (S v) (S i) = S (fix_var v i).
  induction v.
  - destruct i; [ simpl; compute; trivial .. ].
  - destruct i.
    + compute. trivial.
    + specialize (IHv i).
      unfold fix_var in IHv |- *.
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

Lemma insert_kind_get_kind : forall (e e' : env), forall (v : nat),
                                 insert_kind v e e' ->
                                 forall (w : nat), get_kind e w = get_kind e' (fix_var w v).
  induction e.
  - intros.
    destruct e'.
    + simpl. trivial.
    + inversion H.
    + simpl in H. destruct e'.
      * rewrite -> H. simpl. auto.
      * inversion H.
      * inversion H.
  - intros.
    destruct e'.
    + inversion H.
    + simpl. apply IHe. apply H.
    + inversion H.
  - intros.
    destruct e'.
    + inversion H.
    + inversion H.
    + destruct v.
      * simpl in H.
        rewrite H.
        unfold fix_var.
        remember (le_gt_dec 0 w) as le0.
        destruct le0.
        { simpl. auto. }
        { inversion g. }
      * simpl in H.
        destruct w.
        { simpl. destruct H. rewrite H. reflexivity. }
        { rewrite fix_var_s. simpl. apply IHe. apply H. }
Qed.

Lemma insert_kind_wf_typ : forall (t : typ), forall (e e' : env), forall (v : nat), insert_kind v e e' ->
                                                                  wf_typ e t -> wf_typ e' (tshift v t).
  induction t.
  - intros.
    simpl.
    pose proof (insert_kind_get_kind e e' v H n).
    simpl in H0.
    destruct (get_kind e n).
    + unfold fix_var in H1.
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
    simpl.
    simpl in H0.
    apply (IHt (etvar k e) (etvar k e') (S v)).
    simpl.
    split.
    trivial.
    apply H.
    apply H0.
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
    assert ((if le_gt_dec v n then S n else n) = fix_var n v).
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
    