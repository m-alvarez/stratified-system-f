Add LoadPath ".".

Require Import SysF.
Require Import Arith.
Require Import Omega.

Inductive insert_kind : nat -> kind -> env -> env -> Prop :=
| ik_top kind env :
    insert_kind 0 kind env (etvar kind env)
| ik_evar pos kind typ env env' :
    insert_kind pos kind env env' ->
    insert_kind pos kind (evar typ env) (evar (tshift pos typ) env')
| ik_etvar pos kind k env env' :
    insert_kind pos kind env env' ->
    insert_kind (S pos) kind (etvar k env) (etvar k env')
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

Lemma insert_kind_get_kind_1 :
  forall pos kind e e',
    insert_kind pos kind e e' ->
    forall var,
      (var < pos -> get_kind e var = get_kind e' var) /\
      (var > pos -> get_kind e var = get_kind e' (S var)) /\
      (var = pos -> get_kind e' var = Some kind).
  do 5 intro. induction H.
  - intro; repeat split; intro.
    + inversion H.
    + simpl. rewrite H. auto.
  - auto.
  - intros; repeat split; intro; destruct var; auto; try apply IHinsert_kind; omega.
Qed.

Lemma insert_kind_get_kind_2 : 
  forall pos kind e e',
    insert_kind pos kind e e' ->
    forall var,
      get_kind e var = get_kind e' (if le_gt_dec pos var then S var else var).
  do 5 intro.
  induction H; auto with arith.
  - destruct var; auto.
    + rewrite shift_var_s. eauto.
Qed.

Lemma fmap_compose :
  forall A B C f g x, @fmap B C f (@fmap A B g x) = fmap (fun x => f (g x)) x.
  intros. destruct x; auto.
Qed.

Lemma tshift_compose :
  forall T p p',
    tshift p' (tshift (p + p') T) = tshift (S (p + p')) (tshift p' T).
  induction T; intros.
  - unfold tshift.
    destruct (le_gt_dec (p + p') n), (le_gt_dec p' (S n)), (le_gt_dec p' n),
    (le_gt_dec (S (p + p'))); auto; try omega.
  - simpl. congruence.
  - simpl. rewrite plus_n_Sm. congruence.
Qed.

Ltac tvar_case :=
  unfold tshift; unfold tsubst; fold tshift; fold tsubst;
  match goal with
  | |- ?x =>
      match x with
      | context [le_gt_dec ?n ?n'] =>
          case (le_gt_dec n n')
      | context C [(lt_eq_lt_dec ?n ?n')] =>
          case (lt_eq_lt_dec n n'); [intro s; case s; clear s | idtac ]
      end
  end.

Lemma tshift_tsubst_commut_1 :
  forall (T T' : typ) (n n' : nat),
    tshift (n + n') (tsubst T n T') =
    tsubst (tshift (S (n + n')) T) n (tshift (n + n') T').
  induction T; intros;
  [ repeat tvar_case; simpl; trivial; try (intros; f_equal; omega); 
    try (intros; assert False; [ omega | contradiction ]) .. ].
  - f_equal. apply IHT1. apply IHT2.
  - f_equal. assert (S (n + n') = S n + n') by omega. rewrite H.
    assert (n + n' = n + n' + 0) by omega. rewrite H0.
    rewrite (tshift_compose T' (n + n') 0). congruence.
Qed.

Lemma tshift_tsubst_commut_2 :
  forall (T T' : typ) (n n' : nat),
    tshift n (tsubst T (n + n') T') =
    tsubst (tshift n T) (1 + n + n') (tshift n T').
  induction T; intros;
  [ repeat tvar_case; simpl; trivial; auto with arith; try (intros; f_equal; omega) .. ].
  - simpl. f_equal. apply IHT1. apply IHT2.
  - simpl. f_equal. assert (S (n + n') = S n + n') by omega. rewrite H.
    assert (tshift n = tshift (n + 0)) by auto with arith. rewrite H0.
    rewrite tshift_compose. assert (n + 0 = n) by omega. rewrite H1.
    apply IHT.
Qed.

Lemma insert_kind_get_typ :
  forall pos e e' k,
    insert_kind pos k e e' ->
    forall var,
      fmap (tshift pos) (get_typ e var) = get_typ e' var.
  do 5 intro. induction H; intros.
  - auto.
  - destruct var. auto. apply IHinsert_kind.
  - simpl. rewrite <- IHinsert_kind. do 2 rewrite fmap_compose.
    assert (pos = pos + 0) by auto. rewrite H0. 
    destruct (get_typ env var).
    + simpl. rewrite tshift_compose. auto.
    + auto.
Qed.

Lemma insert_kind_wf_typ : forall pos e e' typ kind,
                               insert_kind pos kind e e' ->
                               wf_typ e typ -> wf_typ e' (tshift pos typ).
  intros until typ. generalize pos e e'. clear pos. clear e. clear e'.
  induction typ.
  - intros.
    simpl. erewrite <- insert_kind_get_kind_2; [ eauto .. ].
  - intros. destruct H0. split; [ eauto .. ].
  - intros. simpl in H0. simpl.
    eapply IHtyp.
    eapply ik_etvar.
    apply H.
    apply H0.
Qed.

Lemma remove_kind_wf_typ : forall pos e e' typ kind,
                               insert_kind pos kind e e' ->
                               wf_typ e' (tshift pos typ) -> wf_typ e typ.
  intros until typ. generalize pos e e'. clear pos. clear e. clear e'.
  induction typ.
  - intros.
    simpl. erewrite insert_kind_get_kind_2; [ eauto .. ].
  - intros. destruct H0. split; [ eauto .. ].
  - intros. simpl in H0. simpl.
    eapply IHtyp.
    eapply ik_etvar.
    apply H.
    apply H0.
Qed.

Lemma insert_kind_wf_env : forall pos e e' k,
                               insert_kind pos k e e' ->
                               wf_env e -> wf_env e'.
  do 5 intro.
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

Theorem insert_kind_kinding : forall typ k kind,
                              forall pos e e',
                                insert_kind pos k e e' ->
                                kinding e typ kind -> kinding e' (tshift pos typ) kind.
  induction typ.
  - intros. inversion H0.
    eapply k_tvar.
    { eapply insert_kind_wf_env; [ eauto .. ]. }
    { erewrite <- insert_kind_get_kind_2; [ eauto .. ]. }
    auto.
  - intros. inversion H0.
    eauto using k_tarr.
  - intros. inversion H0.
    eauto using ik_etvar, k_tall.
Qed.

Theorem insert_kind_typing :
  forall (e : env) (t : term) (T : typ),
    typing e t T ->
    forall (e' : env) (pos : nat) (k : kind),
      insert_kind pos k e e' -> typing e' (shift_typ pos t) (tshift pos T).
  do 4 intro. induction H; intros; simpl.
  - apply t_var. eapply insert_kind_wf_env. apply H1. apply H.
    rewrite <- (insert_kind_get_typ pos e e' k). rewrite H0. auto. auto.
  - apply t_abs. apply (insert_kind_wf_typ pos e e' T1 k). apply H1. apply H.
    eapply IHtyping, ik_evar, H1.
  - eapply t_app. eapply IHtyping1, H1. eapply IHtyping2, H1.
  - eapply t_abs_t. eapply IHtyping. eapply ik_etvar. apply H0.
  - assert (pos = 0 + pos) by omega. rewrite H2 at 3. 
    rewrite tshift_tsubst_commut_1. simpl. eapply t_app_t.
    eapply IHtyping. apply H1. 
    eapply insert_kind_kinding. apply H1. apply H0.
Qed.

Inductive env_subst : nat -> typ -> env -> env -> Prop :=
| env_subst_empty var typ :
    env_subst var typ empty empty

| env_subst_etvar_zero typ kind env :
    env_subst 0 typ (etvar kind env) env
| env_subst_etvar_s pos typ kind env env' :
    env_subst pos typ env env' ->
    env_subst (S pos) typ (etvar kind env) (etvar kind env')
              
| env_subst_evar pos typ typ' env env' :
    env_subst pos typ env env' ->
    env_subst pos typ (evar typ' env) (evar (tsubst typ' pos typ) env')
.

Fixpoint remove_var (i : nat) (e : env) :=
  match e with
    | empty => empty
    | evar t e' =>
      match i with
        | 0 => e'
        | S i' => evar t (remove_var i' e')
      end
    | etvar k e' => etvar k (remove_var i e')
  end.

Lemma remove_var_evar :
  forall (p : nat) (e : env) (t : typ),
    evar t (remove_var p e) = remove_var (S p) (evar t e).
  induction p; intros; auto.
Qed.

Definition extends e1 e2 :=
  match (e1, e2) with
    | (Some k, Some k') => k' <= k
    | (None, None) => True
    | _ => False
  end.

Lemma kind_extensionality_wf_typ :
  forall (t : typ) (e e' : env),
    (forall p : nat, extends (get_kind e p) (get_kind e' p)) -> 
    wf_typ e t -> wf_typ e' t.
  induction t.
  - intros. simpl. unfold extends in H. specialize (H n).
    destruct (get_kind e' n); intro; try discriminate.
    simpl in H0. destruct (get_kind e n). inversion H. apply H0. auto.
  - intros. split.
    + eapply IHt1. apply H. apply H0.
    + eapply IHt2. apply H. apply H0.
  - intros. simpl. simpl in H0.
    assert (forall p : nat, extends (get_kind (etvar k e) p) (get_kind (etvar k e') p)).
    destruct p; simpl; auto. unfold extends; trivial. eapply IHt; auto.
Qed.

Lemma kind_extensionality_kinding :
  forall (t : typ) (e : env) (k : kind),
    kinding e t k ->
    forall e',
      wf_env e' ->
      (forall p : nat, extends (get_kind e p) (get_kind e' p)) ->
      kinding e' t k.
  do 4 intro. induction H.
  - intros. specialize (H3 X). unfold extends in H3. rewrite H0 in H3.
    remember (get_kind e' X) as kind_e'_X. destruct kind_e'_X. 
    apply k_tvar with (Kp := k); auto; try omega. inversion H3.
  - intros. eapply k_tall. apply IHkinding. auto. intros. destruct p.
    + simpl. unfold extends. auto.
    + simpl. apply H1.
  - intros. apply k_tarr. apply IHkinding1. apply H1. apply H2. apply IHkinding2.
    apply H1. apply H2.
Qed.

Lemma remove_var_respects_kind_extensionality_strong :
  forall (e : env) (pos : nat),
    forall p : nat, (get_kind e p) = (get_kind (remove_var pos e) p).
  induction e; simpl; intros; auto; try destruct pos; try destruct p; eauto.
Qed.

Lemma equality_implies_extension (a b : option nat) (eq : a = b) : extends a b.
  unfold extends. destruct a, b; auto; try discriminate. inversion eq. omega.
Qed.

Lemma remove_var_respects_kind_extensionality_weak :
  forall (e : env) (pos : nat),
    forall p : nat, extends (get_kind e p) (get_kind (remove_var pos e) p).
  intros. apply equality_implies_extension.
  apply remove_var_respects_kind_extensionality_strong.
Qed.

Lemma remove_var_wf_typ :
  forall (e : env) (pos : nat) (t : typ),
    wf_typ e t -> wf_typ (remove_var pos e) t.
  intros.
  eapply kind_extensionality_wf_typ with (e' := (remove_var pos e)).
  apply remove_var_respects_kind_extensionality_weak.
  apply H.
Qed.

Lemma remove_var_wf_env :
  forall (e : env) (pos : nat),
    wf_env e -> wf_env (remove_var pos e).
  induction e.
  - auto.
  - induction pos.
    + intros. apply H.
    + intros. simpl. split. simpl in H. apply remove_var_wf_typ.
      apply H. apply IHe. apply H.
  - intros. simpl. apply IHe. apply H.
Qed.

Lemma subst_kind_wf_typ :
  forall (T T' : typ) (e e' : env) (pos : nat) (k : kind),
    insert_kind pos k e e' ->
    wf_typ e' T -> 
    wf_typ e T' ->
    wf_typ e (tsubst T pos T').
  induction T; simpl; intros.
  - destruct (lt_eq_lt_dec n pos).
    + destruct s.
      * simpl. rewrite (insert_kind_get_kind_2 pos k e e' H).
        destruct (le_gt_dec pos n). omega. apply H0.
      * apply H1.
    + simpl. rewrite (insert_kind_get_kind_2 pos k e e' H).
      destruct (le_gt_dec pos (n - 1)).
      * assert (S (n - 1) = n) by omega. rewrite H2. auto.
      * omega.
  - split.
    { eapply IHT1. apply H. apply H0. apply H1. }
    { eapply IHT2. apply H. apply H0. apply H1. }
  - eapply IHT. apply ik_etvar. apply H. apply H0.
    eapply insert_kind_wf_typ. apply ik_top. apply H1.
Qed.
    
Lemma add_var_wf_typ :
  forall (e : env) (pos : nat) (t : typ),
    wf_typ (remove_var pos e) t -> wf_typ e t.
  intros.
  eapply kind_extensionality_wf_typ with (e := (remove_var pos e)).
  intro. apply equality_implies_extension. symmetry.
  apply remove_var_respects_kind_extensionality_strong. auto.
Qed.

Lemma remove_var_get_typ_lt :
  forall (e : env) (pos var : nat),
    var < pos ->
    get_typ e var = get_typ (remove_var pos e) var.
  induction e.
  - auto.
  - intros. destruct pos.
    + inversion H.
    + destruct var.
      * auto.
      * apply lt_S_n in H. apply IHe. apply H.
  - intros. simpl. erewrite IHe. reflexivity. auto.
Qed.

Lemma remove_var_get_typ_gt :
  forall (e : env) (pos var : nat),
    var > pos ->
    get_typ e var = get_typ (remove_var pos e) (var - 1).
  induction e.
  - auto.
  - intros. destruct pos.
    + destruct var. inversion H. simpl. rewrite <- minus_n_O. auto.
    + destruct var. inversion H. destruct var. inversion H. inversion H1.
      simpl. pose (IHe pos (S var)). simpl in e0. rewrite <- minus_n_O in e0. apply e0.
      apply lt_S_n in H. apply H.
  - intros. simpl. erewrite IHe. reflexivity. auto.
Qed.

Inductive free_var : nat -> term -> Prop :=
| var_free_var v : free_var v (var v)
| abs_free_var typ body v :
    free_var (S v) body -> free_var v (abs typ body)
| app_free_var_l t1 t2 v : 
    free_var v t1 -> free_var v (app t1 t2)
| app_free_var_r t1 t2 v : 
    free_var v t2 -> free_var v (app t1 t2)
| abs_t_free_var kind term v :
    free_var v term -> free_var v (abs_t kind term)
| app_t_free_var term typ v :
    free_var v term -> free_var v (app_t term typ)
.

Lemma typing_wf_env :
  forall (t : term) (T : typ) (e : env),
    typing e t T -> wf_env e.
  do 4 intro. induction H; [ auto .. ]. apply IHtyping.
Qed.

Lemma weakening_wf_typ_var :
  forall (e : env) (p : nat),
    wf_typ e (tvar (S p)) ->
    wf_typ e (tvar p).
  induction e; intros; auto.
  - apply IHe, H.
  - destruct p; simpl.
    + discriminate.
    + apply IHe. apply H.
Qed.

Lemma weak_extensionality_wf_typ :
  forall (T : typ) (e e' : env),
    (forall p, get_kind e p <> None -> get_kind e' p <> None) ->
    wf_typ e T -> wf_typ e' T.
  induction T; intros; simpl.
  - simpl in H0. specialize (H n). destruct (get_kind e n), (get_kind e' n); [ auto .. ].
  - split; [ eapply IHT1, H0 | eapply IHT2, H0 ]. apply H. apply H.
  - apply (IHT (etvar k e)). intro. destruct p. auto. apply H. apply H0.
Qed.

Lemma kind_weakening_wf_typ :
  forall (T : typ) (e : env) (k : kind),
    wf_typ e T -> wf_typ (etvar k e) T.
  intros.
  apply (weak_extensionality_wf_typ T e (etvar k e)).
  induction p; intros; simpl.
  - discriminate.
  - apply weakening_wf_typ_var. apply H0.
  - apply H.
Qed.

Lemma weakening_wf_typ :
  forall (T : typ) (e : env),
    wf_typ e T ->
    forall (k : kind),
      wf_typ (etvar k e) T.
  induction T; intros; simpl.
  - destruct n; simpl.
    + discriminate.
    + apply weakening_wf_typ_var. apply H.
  - split; [ apply IHT1, H | apply IHT2, H ].
  - apply IHT. simpl in H. apply (weak_extensionality_wf_typ T (etvar k e) (etvar k0 e)).
    { intro. destruct p. discriminate. simpl. auto. }
    apply H.
Qed.
    
Lemma get_typ_wf_typ :
  forall (e : env),
    wf_env e ->
    forall (p : nat),
      match get_typ e p with
        | None => True
        | Some T => wf_typ e T
      end.
  induction e.
  - auto.
  - intro. destruct p.
    + simpl. destruct H. apply (kind_extensionality_wf_typ _ e); auto.
      { unfold extends. simpl. intro. destruct (get_kind e p); auto. }
    + assert (wf_env e). apply H. simpl.
      assert (match get_typ e p with | Some T => wf_typ e T | None => True end).
      apply IHe. apply H0.
      destruct (get_typ e p); auto.
      apply (kind_extensionality_wf_typ _ e); auto.
      { intro. simpl. unfold extends. destruct (get_kind e p0); auto. } 
  - intros. destruct p; simpl.
    + specialize (IHe H 0).
      destruct (get_typ e 0).
      * simpl. eapply insert_kind_wf_typ. apply ik_top. apply IHe.
      * auto.
    + specialize (IHe H (S p)). destruct (get_typ e (S p)).
      * simpl. eapply insert_kind_wf_typ. apply ik_top. apply IHe.
      * auto. 
Qed.

Lemma kinding_wf_typ :
  forall (T : typ) (e : env) (k : kind),
    kinding e T k -> wf_typ e T.
  do 4 intro. induction H; simpl; intros.
  - intro. assert (Some Kp = None). transitivity (get_kind e X). auto. auto. discriminate.
  - apply IHkinding.
  - split. { apply IHkinding1. } { apply IHkinding2. }
Qed.

Lemma kinding_wf_env :
  forall (T : typ) (e : env) (k : kind),
    kinding e T k -> wf_env e.
  do 4 intro. induction H; simpl; intros; auto.
Qed.

Lemma typing_wf_typ :
  forall (t : term) (T : typ) (e : env),
    typing e t T -> wf_typ e T.
  do 4 intro. induction H.
  - pose (get_typ_wf_typ e H X). rewrite H0 in y. apply y.
  - split. apply H. apply (kind_extensionality_wf_typ T2 (evar T1 e)); auto.
    intro. unfold extends. simpl. destruct (get_kind e p); auto.
  - apply IHtyping1.
  - apply IHtyping.
  - simpl in IHtyping.
    eapply subst_kind_wf_typ. apply ik_top. apply IHtyping. eapply kinding_wf_typ. apply H0.
Qed.

Lemma kinding_extensionality :
  forall (T : typ) (k : kind) (e : env),
    kinding e T k ->
    forall (e' : env),
      (forall p, extends (get_kind e p) (get_kind e' p)) ->
      wf_env e' ->
      kinding e' T k.
  do 4 intro. induction H; intros; simpl.
  - pose H2. specialize (e0 X).
    unfold extends in e0. remember (get_kind e X) as kind_e_X. destruct kind_e_X; simpl.
    + remember (get_kind e' X) as kind_e'_X. destruct kind_e'_X; try omega. 
      apply k_tvar with (Kp := k0); auto. inversion H0. omega.
    + discriminate.
  - eapply k_tall. apply IHkinding. intro. 
    destruct p. { simpl. unfold extends. auto. } { simpl. apply H0. }
    apply H1.
  - apply k_tarr.
    { apply IHkinding1. apply H1. apply H2. }
    { apply IHkinding2. apply H1. apply H2. }
Qed.

Lemma typing_extensionality :
  forall (t : term) (T : typ) (e : env),
    typing e t T ->
    forall (e' : env),
      (forall p, extends (get_kind e p) (get_kind e' p)) ->
      (forall p, free_var p t -> get_typ e p = get_typ e' p) ->
      wf_env e' ->
      typing e' t T.
  do 4 intro. induction H.
  - intros. apply t_var. apply H3. rewrite <- H2. apply H0.
    apply var_free_var.
  - intros. apply t_abs.
    eapply kind_extensionality_wf_typ. apply H1. apply H.
    apply IHtyping.
    { intro. simpl. apply H1. }
    { intros. destruct p. auto. simpl. apply H2. apply abs_free_var, H4. }
    { split. eapply kind_extensionality_wf_typ. apply H1. 
      apply typing_wf_env in H0. apply H0. apply H3. }
  - intros. eapply t_app.
    + eapply IHtyping1.
      * apply H1.
      * intros. eapply app_free_var_l in H4. apply H2, H4.
      * apply H3.
    + eapply IHtyping2.
      * apply H1.
      * intros. eapply app_free_var_r in H4. apply H2, H4.
      * apply H3.
  - intros. apply t_abs_t.
    apply IHtyping.
    { intro. destruct p; simpl. unfold extends; auto. apply H0. }
    { intros. simpl. rewrite H1. auto. apply abs_t_free_var. apply H3. }
    { apply H2. }
  - intros. eapply t_app_t. apply IHtyping. apply H1.
    { intros. apply H2. apply app_t_free_var. apply H4. }
    { apply H3. }
    { eapply kind_extensionality_kinding. apply H0. apply H3. apply H1. }
Qed.

Lemma typing_weakening_var_ind :  
  forall (e : env) (pos : nat) (t : term) (T : typ),
    wf_env e -> typing (remove_var pos e) t T -> typing e (shift pos t) T.
  intros e pos t T H1 H2; cut (exists e', e' = remove_var pos e). intros (e', E).
  rewrite <- E in H2. generalize pos e E H1. clear pos e E H1.
  induction H2; intros pos e' E H1; simpl.
  - apply t_var. apply H1.
    destruct (le_gt_dec pos X).
    + assert (S X > pos) by omega.
      apply (remove_var_get_typ_gt e' _ (S X)) in H2. simpl in H2.
      rewrite H2. rewrite <- minus_n_O. rewrite <- H0. rewrite E. auto.
    + apply (remove_var_get_typ_lt e' _ X) in g. rewrite g. rewrite <- E. rewrite <- H0. auto.
  - apply t_abs. eapply add_var_wf_typ. rewrite E in H. apply H. apply IHtyping.
    + rewrite E. auto.
    + split. apply typing_wf_env in H2. destruct H2. rewrite E in H.
      eapply add_var_wf_typ. apply H. apply H1.
  - eapply t_app. apply IHtyping1. apply E. apply H1. apply IHtyping2. apply E. apply H1.
  - eapply t_abs_t. apply IHtyping. rewrite E. auto.
    simpl. apply H1.
  - eapply t_app_t. apply IHtyping. apply E. apply H1.
    eapply kinding_extensionality.
    { apply H. }
    { rewrite E. intro. apply equality_implies_extension. symmetry.
      apply remove_var_respects_kind_extensionality_strong. }
    { apply H1. }
  - exists (remove_var pos e). auto.
Qed.

Lemma typing_weakening_var :
  forall (e : env) (t : term) (T T' : typ),
  wf_env e -> wf_typ e T' -> typing e t T -> typing (evar T' e) (shift 0 t) T.
  intros.
  eapply typing_weakening_var_ind.
  split. apply H0. apply H. simpl. apply H1.
Qed.

Lemma subst_preserves_typing :
  forall (t u : term),
  forall (V W : typ),
  forall (e : env) (x : nat),
    typing e t V ->
    typing (remove_var x e) u W ->
    get_typ e x = Some W ->
    typing (remove_var x e) (subst t x u) V.
  intros t u V W e x H. generalize u W x. clear u W x.
  induction H; simpl; intros.
  - case (lt_eq_lt_dec X x).
    + intro. destruct s.
      * eapply t_var. apply remove_var_wf_env. apply H.
        rewrite <- H0. symmetry.
        apply remove_var_get_typ_lt. apply l.
      * assert (T = W). symmetry in H2. rewrite e0 in H0.
        apply (eq_trans H2) in H0. inversion H0. auto. rewrite <- H3 in H1. auto.
    + intro. eapply t_var. apply remove_var_wf_env. apply H.
      rewrite <- H0. symmetry. apply remove_var_get_typ_gt. apply l.
  - subst. apply t_abs.
    specialize (IHtyping (shift 0 u) W (S x)). simpl in IHtyping.
    apply remove_var_wf_typ, H. rewrite remove_var_evar. apply IHtyping with (W := W).
    simpl. apply typing_weakening_var. apply remove_var_wf_env.
    apply typing_wf_env in H0. apply H0. apply remove_var_wf_typ. apply H.
    apply H1. apply H2.
  - eapply t_app.
    eapply IHtyping1. apply H1. apply H2. eapply IHtyping2. apply H1. apply H2.
  - eapply t_abs_t.
    eapply IHtyping. 
    eapply (insert_kind_typing (remove_var x e) u). apply H0.
    apply ik_top.
    rewrite <- (insert_kind_get_typ 0 e (etvar K e) K). rewrite H1. auto.
    apply ik_top.
  - eapply t_app_t. eapply IHtyping. apply H1. apply H2.
    eapply kinding_extensionality. apply H0.
    apply remove_var_respects_kind_extensionality_weak.
    apply remove_var_wf_env.
    eapply typing_wf_env.
    apply H.
Qed.

Theorem wf_typ_kinding :
  forall (T : typ) (e : env),
    wf_env e ->
    wf_typ e T ->
    exists (k : kind), kinding e T k.
  induction T; simpl; intros.
  - remember (get_kind e n) as o. destruct o.
    + idtac. exists k. eapply k_tvar. apply H. symmetry. apply Heqo. auto.
    + exfalso. auto.
  - destruct H0. apply IHT1 in H0; auto. apply IHT2 in H1; auto. destruct H0, H1.
    + idtac. exists (max x x0). apply k_tarr; auto.
  - apply IHT in H0; auto. destruct H0. exists (S (max x k)). apply k_tall. auto.
Qed.

Theorem regularity :
  forall (e : env) (t : term) (T : typ),
    typing e t T ->
    exists (k : kind), kinding e T k.
  intros. apply wf_typ_kinding; eauto using typing_wf_env, typing_wf_typ.
Qed.

Lemma replace_kind_respects_kind_extensionality :
  forall (e e' e'' : env) (k' k'' : kind) (pos : nat),
    k'' <= k' ->
    insert_kind pos k' e e' ->
    insert_kind pos k'' e e'' ->
    (forall (p : nat), extends (get_kind e' p) (get_kind e'' p)).
  intros.
  { destruct (gt_eq_gt_dec pos p). destruct s.
    + pose insert_kind_get_kind_2. specialize (e0 pos _ _ _ H0 (pred p)).
      pose insert_kind_get_kind_2. specialize (e1 pos _ _ _ H1 (pred p)).
      erewrite <- S_pred in e0, e1. destruct (le_gt_dec pos (pred p)); try omega.
      * rewrite <- e0. rewrite <- e1. apply equality_implies_extension. auto.
      * apply g. * apply g.
    + pose insert_kind_get_kind_1. specialize (a pos _ _ _ H0 p). destruct a. destruct H3.
      pose insert_kind_get_kind_1. specialize (a pos _ _ _ H1 p). destruct a. destruct H6.
      rewrite H4, H7; auto.
    + pose insert_kind_get_kind_1. specialize (a pos _ _ _ H0 p). destruct a. 
      pose insert_kind_get_kind_1. specialize (a pos _ _ _ H1 p). destruct a. 
      rewrite <- H2, H4; auto. apply equality_implies_extension; auto. }
Qed.

Lemma replace_kind_wf_typ :
  forall (T : typ),
  forall (e e' e'' : env) (k' k'' : kind) (pos : nat),
    k'' <= k' ->
    insert_kind pos k' e e' ->
    insert_kind pos k'' e e'' ->
    wf_typ e' T ->
    wf_typ e'' T.
  intros.
  eapply kind_extensionality_wf_typ.
  eapply replace_kind_respects_kind_extensionality.
  apply H. apply H0. apply H1. apply H2.
Qed.

Lemma insert_kind_swap :
  forall (e : env) (T : typ) (k: kind),
    insert_kind 0 k (evar T e) (etvar k (evar T e)) ->
    insert_kind 0 k (evar T e) (evar (tshift 0 T) (etvar k e)).
  intros. apply ik_evar. apply ik_top.
Qed.

Lemma replace_kind_wf_env :
  forall (e : env),
    forall (e'' e' : env) (k'' k' : kind) (pos : nat),
      insert_kind pos k'' e e'' /\ insert_kind pos k' e e' ->
      k'' <= k' ->
      wf_env e' ->
      wf_env e''.
  induction e.
  - intros. inversion H. inversion H2. simpl. auto.
  - intros. destruct H.
    remember (evar t e) in H.
    induction H; simpl; auto; try discriminate.
    + remember (evar t e) in H2.
      inversion H2; simpl; auto; try discriminate.
      * simpl. rewrite <- H5 in H1. rewrite Heqe0. rewrite <- Heqe1. apply H1.
      * simpl. rewrite <- H5 in *. rewrite Heqe0. rewrite <- Heqe1.
        rewrite <- H6 in H1. split.
        { clear H5 e0 H4 kind0 H3 pos. rewrite <- H6 in H2. inversion H2.
          clear H4 pos H9 env'0 H5 kind0 H8 env1 H3 typ0.
          inversion Heqe1. rewrite -> H5 in *. clear H5 env0. rewrite -> H4 in *.
          clear H4 typ. clear H6 e'. clear H. clear Heqe0. clear Heqe1.
          destruct H1. eapply remove_kind_wf_typ. 
          apply H7. apply H. }
        { inversion Heqe1. rewrite H9, H8 in *. clear H3 H4 H8 H9. clear H5 e0.
          eapply (IHe (etvar kind e)). split; auto.
          { eapply ik_top. } { rewrite <- H6 in H2. inversion H2. apply H7. }
          auto. apply H1. }
    + split. 
      * eapply insert_kind_wf_typ. apply H. inversion Heqe0.
        rewrite H5 in *.
        clear H4 H5 Heqe0 typ env.
        remember (evar t e) in H2. inversion H2; simpl; auto; try discriminate.
        { rewrite <- H3 in *. clear H3 pos. clear H4 kind0. clear H5. rewrite <- H6 in *.
          rewrite Heqe0 in H1. apply H1. }
        { rewrite <- H7 in H1. destruct H1. rewrite Heqe0 in *. clear Heqe0 e0.
          rewrite <- H7 in *. clear H7 e'. inversion H6. rewrite H9 in *. clear H9 typ.
          rewrite H10 in *. clear H10 env. clear H4 pos0. clear H5 kind0. clear H6.
          eapply remove_kind_wf_typ. apply H3. apply H1. }
        { rewrite <- H6 in *. discriminate. } 
      * remember (evar t e) in H2. inversion H2; simpl; auto; try discriminate. 
        { clear H5 env0. clear H4 kind0. rewrite <- H3 in *. clear pos H3.
          rewrite <- H6 in *. clear H6 e'. 
          inversion Heqe0. rewrite H5 in *. clear H5 env Heqe0. clear H4.
          rewrite Heqe1 in *. clear Heqe1 e0. clear IHinsert_kind.
          eapply ik_evar with (typ := t) in H.
          eapply IHe. split. inversion H. apply H6. apply ik_top. apply H0. apply H1. }
        { rewrite Heqe1 in *. clear Heqe1 e0. inversion Heqe0. rewrite H10 in *.
          clear Heqe0 H9 H10 typ env. clear H4 pos0. clear H5 kind0. inversion H6.
          rewrite H5 in *. clear H5 typ0. rewrite H8 in *. clear H8 env0. clear H6.
          rewrite <- H7 in *. clear H7 e'. eapply IHe. split.
          { apply H. } { apply H3. } { apply H0. } { apply H1. } }
        { rewrite <- H6 in *. discriminate. }
  - intros. destruct H. remember (etvar k e) in H.
    inversion H.
    + rewrite <- H3 in *. rewrite Heqe0 in *. rewrite <- H6 in *. inversion H2.
      rewrite <- H10 in H2. simpl. 
      eapply (IHe (etvar k'' e)). split. apply ik_top. apply ik_top.
      apply H0. rewrite <- H10 in H1. apply H1.
    + rewrite <- H6 in Heqe0. inversion Heqe0.
    + rewrite <- H6 in Heqe0. inversion Heqe0. 
      (* As I write this, it's 6:30 AM and I haven't slept *)
      (* This can probably be done in a much shorter way. *)
      rewrite H9, H10 in *. clear H9 H10 H5 k0 env kind.
      rewrite <- H6, <- H7 in *. clear H6 H7 e0 e''. clear Heqe0. rewrite <- H4 in *.
      clear H4 pos. remember (etvar k e) in H2.
      inversion H2. rewrite <- H7 in *. clear H7 e0. clear H6 kind. clear H5 pos.
      rewrite <- H8 in *. clear H8 e'. inversion Heqe0. 
      rewrite <- H7, <- H8 in *. clear H7 H8 e0 e'. rewrite <- H4 in *. clear H4 pos0.
      clear H6. simpl. eapply IHe. split. apply H3. inversion Heqe0. rewrite H7 in *.
      apply H5. auto. apply H1.
Qed.
(* As I finish this proof, I know this is the most satisfying moment of my life *)
      
Theorem narrowing :
  forall (e' : env) (t : term) (T : typ),
    typing e' t T ->
    forall (pos : nat) (e e'' : env) (k' k'' : kind),
    insert_kind pos k' e e' ->
    insert_kind pos k'' e e'' ->
    k'' <= k' ->
    typing e'' t T.
  intros.
  eapply typing_extensionality. apply H.
  eapply replace_kind_respects_kind_extensionality. apply H2. apply H0. apply H1.
  { intros.
    pose (insert_kind_get_typ _ _ _ _ H0 p).
    pose (insert_kind_get_typ _ _ _ _ H1 p).
    rewrite <- e0, e1. auto. }
  eapply replace_kind_wf_env. split. apply H1. apply H0. apply H2.
  eapply typing_wf_env. apply H.
Qed.