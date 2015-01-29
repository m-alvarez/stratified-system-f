Add LoadPath ".".

Require Import SysF.
Require Import Arith.
Require Import Omega.

Inductive insert_kind : nat -> env -> env -> Prop :=
| ik_top kind env :
    insert_kind 0 env (etvar kind env)
| ik_evar pos typ env env' :
    insert_kind pos env env' ->
    insert_kind pos (evar typ env) (evar (tshift pos typ) env')
| ik_etvar pos kind env env' :
    insert_kind pos env env' ->
    insert_kind (S pos) (etvar kind env) (etvar kind env')
.

Lemma shift_var_s : forall var shift,
                      (if le_gt_dec (S shift) (S var) then S (S var) else S var) =
                      S (if le_gt_dec shift var then S var else var).
  intros.
  induction var.
  - destruct shift; [ auto .. ].
  - destruct (le_gt_dec shift var) eqn:shift_le_var,
             (le_gt_dec (S shift) (S (S var))) eqn:Sshift_le_SSvar,
             (le_gt_dec shift (S var)) eqn:shift_le_Svar;
    [ omega .. ].
Qed.

Hint Rewrite shift_var_s : core.
    
Lemma insert_kind_get_kind : forall pos e e',
                               insert_kind pos e e' ->
                               forall var,
                                 get_kind e var = get_kind e' (if le_gt_dec pos var then S var else var).
  do 4 intro.
  induction H.
  - auto with arith.
  - auto.
  - destruct var.
    + auto.
    + rewrite shift_var_s. eauto.
Qed.

Theorem insert_kind_wf_typ : forall pos e e' typ,
                               insert_kind pos e e' ->
                               wf_typ e typ -> wf_typ e' (tshift pos typ).
  intros until typ. generalize pos e e'. clear pos. clear e. clear e'.
  induction typ.
  - intros.
    simpl. erewrite <- insert_kind_get_kind; [ eauto .. ].
  - intros. destruct H0. split; [ eauto .. ].
  - intros. simpl in H0. simpl.
    eapply IHtyp.
    eapply ik_etvar.
    apply H.
    apply H0.
Qed.

Theorem insert_kind_wf_env : forall pos e e',
                               insert_kind pos e e' ->
                               wf_env e -> wf_env e'.
  do 4 intro.
  induction H.
  - auto.
  - intro. simpl.
    split.
    + eapply insert_kind_wf_typ.
      apply H.
      apply H0.
    + apply IHinsert_kind.
      apply H0.
  - intro. apply IHinsert_kind. apply H0.
Qed.

Theorem insert_kind_kinding : forall typ kind,
                              forall pos e e',
                                insert_kind pos e e' ->
                                kinding e typ kind -> kinding e' (tshift pos typ) kind.
  induction typ.
  - intros. inversion H0.
    eapply k_tvar.
    { eapply insert_kind_wf_env; [ eauto .. ]. }
    { erewrite <- insert_kind_get_kind; [ eauto .. ]. }
    auto.
  - intros. inversion H0.
    eauto using k_tarr.
  - intros. inversion H0.
    eauto using ik_etvar, k_tall.
Qed.

Lemma insert_kind_get_typ : forall pos,
                            forall var e e',
                              insert_kind pos e e' ->
                              wf_env e ->
                              match get_typ e var with
                                | None => get_typ e' var = None
                                | Some t => get_typ e' var = Some (tshift pos t)
                              end.
  - intros until pos. generalize var. 
    
Theorem insert_kind_typing : forall term typ,
                             forall pos e e',
                               insert_kind pos e e' ->
                               typing e term typ -> typing e' term (tshift pos typ).
  induction term.
  - intros. eapply t_var. inversion H0.
    eapply insert_kind_wf_env. eauto. auto.
