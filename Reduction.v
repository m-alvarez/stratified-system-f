(** Formalization of a Predicative System F

In this file, we study reduction by providing:

  * a definition of our reduction relation and its (reflexive and
    usual) transitive closures ;
  * a definition for normal and neutral terms ;
  * proofs of correctness and completeness for these definitions ;
  * proofs that normal and neutral terms are preserved by type
    substitution. *)

Require Import Relations.

Add LoadPath ".".

(* Use [make SysF.vo] to compile SysF.v before executing this line. *)
Require Import SysF.

(** [reduction t t'] is an inductive predicate that says that [t']
    can be obtained from [t] by one step of (either type or term)
    beta reduction, possibly in a context (this is what we call
    congruence). *)
Inductive reduction : term -> term -> Prop :=
| beta_app T t t' :
    reduction (app (abs T t) (t')) (subst t 0 t')
| beta_app_t k t T :
    reduction (app_t (abs_t k t) T) (subst_typ t 0 T)
| congr_abs T t t' :
    reduction t t' -> reduction (abs T t) (abs T t')
| congr_abs_t k t t' :
    reduction t t' -> reduction (abs_t k t) (abs_t k t')
| congr_app_left t1 t1' t2 :
    reduction t1 t1' ->
    reduction (app t1 t2) (app t1' t2)
| congr_app_right t1 t2 t2' :
    reduction t2 t2' ->
    reduction (app t1 t2) (app t1 t2')
| congr_app_t t t' T :
    reduction t t' ->
    reduction (app_t t T) (app_t t' T).

(** [x ~> y] is a notation for [reduction x y]. *)
Notation "x ~> y" := (reduction x y) (at level 80).

(** [x ~>* y] is a notation for the reflexive and transitive closure of
    our reduction. That is, [t ~>* t'] says that [t'] can be obtained from
    [t] by zero, one or several steps of this reduction. *)
Notation "x ~>* y" := (clos_refl_trans term reduction x y) (at level 80).

(** [x ~>+ y] is a notation for the transitive closure of our reduction.
    That is, [t ~>+ t'] says that [t'] can be obtained from [t] by one
    or several steps of this reduction. *)
Notation "x ~>+ y" := (clos_trans term reduction x y) (at level 80).

(** This tactic can be used to show [t ~> t'] when we
    know enough about [t] and [t'] to conclude. *)
Ltac one_step :=
  simpl; (
    eauto
      || eapply beta_app
      || eapply beta_app_t
      || (((eapply congr_app_left)
             || (eapply congr_app_right)
             || (eapply congr_app_t)
             || (eapply congr_abs)
             || (eapply congr_abs_t)); one_step)
  ).

(** This tactic can be used to show [t ~>* t'] when the required
    hypotheses are available.

WARNING: This can loop. *)
Ltac steps_unbound :=
  simpl;
  match goal with
    | |- _ ~> _ => one_step
    | |- _ ~>+ _ =>
      (eapply t_step; one_step) || (eapply t_trans; [ (eauto || steps_unbound) .. ])
    | |- _ ~>* _ =>
      (eapply rt_step; one_step) || (eapply rt_refl) || (eapply rt_trans; [ (eauto || steps_unbound) .. ])
  end.

(** This tactic can be used to show [t ~>* t'] or [t ~>+ t']
    in finite time when we know enough about [t] and [t'] to
    conclude. *)
Ltac steps := timeout 2 steps_unbound.

Section Examples.

  Variable T : typ.

  (** This example shows a one step direct reduction:
        (\x. x) y ~> y *)
  Example test : app (abs T (var 0)) (var 0) ~> var 0.
  Proof.
    one_step.
  Qed.

  (** This example shows a one step congruence reduction:
      (\y. (\x. x) y) ~> (\y. y) *)
  Example test2 : abs T (app (abs T (var 0)) (var 0)) ~> abs T (var 0).
  Proof.
    one_step.
  Qed.

  (** This example shows a two step reduction:
        (\x. x) ((\x. x) y) ~> (\x. x) y ~> y *)
  Example test3 : let t := (app (abs T (var 0)) (app (abs T (var 0)) (var 0))) in
                  let t' := var 0 in
                  t ~>* t' /\ t ~>+ t'.
  Proof.
    split; steps.
  Qed.

End Examples.

(**********************
 * Congruence for ~>* *
 **********************)
Section StepsCongruence.

  (** This theorem states that ~>* may be applied in
      any abstraction context. *)
  Theorem steps_congruence_abs (t t' : term) :
    t ~>* t' -> forall T, abs T t ~>* abs T t'.
    intros. induction H; steps.
  Qed.

  (** This theorem states that ~>* may be applied in
      any type abstraction context. *)
  Theorem steps_congruence_abs_t (t t' : term) :
    t ~>* t' -> forall k, abs_t k t ~>* abs_t k t'.
    intros. induction H; steps.
  Qed.

  (** This theorem proves that ~>* may be applied in
      any left application context. *)
  Theorem steps_congruence_app_left (t t' : term) :
    t ~>* t' -> forall t1, app t t1 ~>* app t' t1.
    intros. induction H; steps.
  Qed.

  (** This theorem proves that ~>* may be applied in
      any right application context. *)
  Theorem steps_congruence_app_right (t t' : term) :
    t ~>* t' -> forall t1, app t1 t ~>* app t1 t'.
    intros. induction H; steps.
  Qed.

  (** This theorem proves that ~>* may be applied in
      any type application context. *)
  Theorem steps_congruence_app_t (t t' : term) :
    t ~>* t' -> forall T, app_t t T ~>* app_t t' T.
    intros. induction H; steps.
  Qed.

End StepsCongruence.

(**********************
 * Congruence for ~>+ *
 **********************)
Section ManyStepsCongruence.

  (** This theorem states that ~>+ may be applied in
      any abstraction context. *)
  Theorem many_steps_congruence_abs (t t' : term) :
    t ~>+ t' -> forall T, abs T t ~>+ abs T t'.
    intros. induction H; steps.
  Qed.

  (** This theorem states that ~>+ may be applied in
      any type abstraction context. *)
  Theorem many_steps_congruence_abs_t (t t' : term) :
    t ~>+ t' -> forall k, abs_t k t ~>+ abs_t k t'.
    intros. induction H; steps.
  Qed.

  (** This theorem proves that ~>+ may be applied in
      any left application context. *)
  Theorem many_steps_congruence_app_left (t t' : term) :
    t ~>+ t' -> forall t1, app t t1 ~>+ app t' t1.
    intros. induction H; steps.
  Qed.

  (** This theorem proves that ~>+ may be applied in
      any right application context. *)
  Theorem many_steps_congruence_app_right (t t' : term) :
    t ~>+ t' -> forall t1, app t1 t ~>+ app t1 t'.
    intros. induction H; steps.
  Qed.

  (** This theorem proves that ~>+ may be applied in
      any type application context. *)
  Theorem many_steps_congruence_app_t (t t' : term) :
    t ~>+ t' -> forall T, app_t t T ~>+ app_t t' T.
    intros. induction H; steps.
  Qed.

End ManyStepsCongruence.

(********************************************
 * Definitions for normal and neutral terms *
 ********************************************)

Inductive normal : term -> Prop :=
| normal_neutral t : neutral t -> normal t
| normal_abs T t : normal t -> normal (abs T t)
| normal_abs_t k t : normal t -> normal (abs_t k t) 

with neutral : term -> Prop :=
     | neutral_var n : neutral (var n)
     | neutral_app t1 t2 : neutral t1 -> normal t2 -> neutral (app t1 t2)
     | neutral_app_t t T : neutral t -> neutral (app_t t T)
.

(** This tactic can be used to show [neutral t] when
    we know enough about [t] to conclude. *)
Ltac neutralize :=
  simpl;
  (eauto
     || match goal with
          | |- neutral (var _) => (apply neutral_var)
          | |- neutral (app_t _ _) => (apply neutral_app_t; neutralize)
          | |- neutral (app _ _) => (apply neutral_app; [ neutralize | normalize ])
        end)
  (** This tactic can be used to show [normal t] when
      we know enough about [t] to conclude. *)
  with normalize :=
  simpl;
  (eauto 
     || match goal with
          | |- normal (abs _ _) => (apply normal_abs; normalize)
          | |- normal (abs_t _ _) => (apply normal_abs_t; normalize)
          | |- normal _ => (apply normal_neutral; neutralize)
        end).

(***********************************************************************
 * Proofs of correctness and completeness for the previous definitions *
 ***********************************************************************)

Section CorrectnessAndCompleteness.

  Lemma normality_neutrality_correctness (t : term) (H : normal t \/ neutral t) :
    forall t', ~ (t ~> t').
    induction t; intros; intro; inversion H0.
    - apply IHt in H4. apply H4. destruct H; inversion H.
      inversion H5. left. apply H6.
    - case H; intro; rewrite <- H2 in *; inversion H4;
      [ inversion H5; inversion H9 | inversion H7 ].
    - apply IHt1 in H4. apply H4. destruct H; inversion H.
      + inversion H5. right. apply H9.
      + right. apply H7.
    - apply IHt2 in H4. apply H4. destruct H; inversion H.
      + inversion H5. left. apply H10.
      + left. apply H8.
    - apply IHt in H4. apply H4. destruct H; inversion H; [ inversion H5 | left; apply H6 ].
    - destruct H; inversion H; rewrite <- H2 in *.
      + inversion H4. inversion H7.
      + inversion H5.
    - apply IHt in H4. apply H4. destruct H; inversion H.
      + inversion H5. right. apply H8.
      + right. apply H6.
  Qed.
  
  Lemma normality_correctness (t : term) (H : normal t) (t' : term) : ~ (t ~> t').
    eauto using normality_neutrality_correctness.
  Qed.
  
  (* Stuck terms are incorrect terms that can't be reduced further *)
  Inductive stuck : term -> Prop :=
  | stuck_app k t t' : stuck (app (abs_t k t) t')
  | stuck_app_t T t T' : stuck (app_t (abs T t) T')
                               
  | stuck_congr_abs T t : stuck t -> stuck (abs T t)
  | stuck_congr_abs_t k t : stuck t -> stuck (abs_t k t)
                                             
  | stuck_congr_app_l t1 t2 : stuck t1 -> stuck (app t1 t2)
  | stuck_congr_app_r t1 t2 : stuck t2 -> stuck (app t1 t2)
  | stuck_congr_app_t t T : stuck t -> stuck (app_t t T).
  
  Ltac make_stuck :=
    simpl; (eauto 
              || (apply stuck_app)
              || (apply stuck_app_t)
              || (apply stuck_congr_abs; make_stuck)
              || (apply stuck_congr_abs_t; make_stuck)
              || (apply stuck_congr_app_l; [ make_stuck .. ])
              || (apply stuck_congr_app_r; [ make_stuck .. ])
              || (apply stuck_congr_app_t; make_stuck)).
  
  Lemma normality_completeness (t : term) :
    (forall t', ~(t ~> t')) -> normal t \/ stuck t.
    induction t; intros.
    - left. normalize.
    - assert (normal t0 \/ stuck t0).
      { apply IHt. intros. intro. apply (H _ (congr_abs _ _ _ H0)). }
      destruct H0; [ left; normalize | right; make_stuck ].
    - assert (normal t1 \/ stuck t1).
      { apply IHt1. intros. intro. apply (H _ (congr_app_left _ _ _ H0)). }
      assert (normal t2 \/ stuck t2).
      { apply IHt2. intros. intro. apply (H _ (congr_app_right _ _ _ H1)). }
      destruct H0, H1; try (right; make_stuck).
      + destruct t1.
        * left. normalize.
        * exfalso. apply (H (subst t1 0 t2)). one_step.
        * left. inversion H0. eapply neutral_app in H2. apply normal_neutral. eauto. auto.
        * right. make_stuck.
        * left. inversion H0. normalize.
    - assert (normal t \/ stuck t).
        apply IHt. intros. intro. apply (H (abs_t k t')). one_step.
        destruct H0; [ left; normalize | right; make_stuck ].
      - assert (normal t \/ stuck t).
        { apply IHt. intros. intro. apply (H (app_t t' t0)). one_step. }
        destruct H0; try (right; make_stuck).
        + destruct t.
          * left. normalize.
          * right. make_stuck.
          * left. inversion H0. normalize.
          * exfalso. apply (H (subst_typ t 0 t0)). one_step.
          * left. inversion H0. normalize.
    Qed.

End CorrectnessAndCompleteness.

(*************************************
 * Preservation by type substitution *
 *************************************)

Lemma normality_neutrality_preservation :
  forall (t : term) (pos : nat) (T : typ),
    (normal t -> normal (subst_typ t pos T))
    /\ (neutral t -> neutral (subst_typ t pos T)).
  induction t; intros; simpl; try auto || split; intro.
  - apply normal_abs. apply IHt. inversion H. inversion H0. normalize.
  - inversion H.
  - inversion H. inversion H0. apply normal_neutral, neutral_app.
    + apply IHt1. neutralize.
    + apply IHt2. neutralize.
  - inversion H. apply neutral_app.
    + apply IHt1. neutralize.
    + apply IHt2. neutralize.
  - apply normal_abs_t. apply IHt. inversion H. inversion H0. normalize. 
  - inversion H.
  - inversion H. inversion H0. apply normal_neutral. apply neutral_app_t. apply IHt. neutralize.
  - inversion H. apply neutral_app_t. apply IHt. neutralize.
Qed.

Theorem normality_is_preserved_by_type_substitution (t : term) (H : normal t) :
  forall (pos : nat) (T : typ), normal (subst_typ t pos T).
  intros. apply normality_neutrality_preservation. auto.
Qed.

Theorem neutrality_is_preserved_by_type_substitution (t : term) (H : neutral t) :
  forall (pos : nat) (T : typ), neutral (subst_typ t pos T).
  intros. apply normality_neutrality_preservation. auto.
Qed.
