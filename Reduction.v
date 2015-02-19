Add LoadPath ".".

Require Import SysF.
Require Import Relations.

Inductive reduction : term -> term -> Prop :=
| beta_app T t t' :
    reduction (app (abs T t) (t')) (subst t 0 t')
| beta_app_t k t T :
    reduction (app_t (abs_t k t) T) (subst_typ t 0 T)
| congr_abs T t t' :
    reduction t t' -> reduction (abs T t) (abs T t')
| congr_abs_t k t t' :
    reduction t t' -> reduction (abs_t k t) (abs_t k t')
(* Question: which rule is right!? *)
| congr_app_left t1 t1' t2 :
    reduction t1 t1' ->
    reduction (app t1 t2) (app t1' t2)
| congr_app_right t1 t2 t2' :
    reduction t2 t2' ->
    reduction (app t1 t2) (app t1 t2')
| congr_app_t t t' T :
    reduction t t' ->
    reduction (app_t t T) (app_t t' T).

Notation "x ~> y" := (reduction x y) (at level 80).
Notation "x ~>* y" := (clos_trans term reduction x y) (at level 80).

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

(* WARNING: this can loop *)
Ltac steps_unbound :=
  simpl;
  match goal with
    | |- _ ~> _ => one_step
    | |- _ ~>* _ =>
      (eapply t_step; one_step) || (eapply t_trans; [ (eauto || steps_unbound) .. ])
  end.

Ltac steps := timeout 2 steps_unbound.

Section examples.
  Variable T : typ.
  Example test : (app (abs T (var 0)) (var 1)) ~> var 1.
  Proof.
    one_step.
  Qed.
  
  Example test2 : (app (abs T (var 0)) (app (abs T (var 0)) (var 1))) ~>* var 1.
  Proof.
    steps.
  Qed.
End examples.

(**********************
 * Congruence for ~>* *
 **********************)

Lemma many_steps_congruence_abs (t t' : term) :
  t ~>* t' -> forall T, abs T t ~>* abs T t'.
  intros. induction H; steps.
Qed.

Lemma many_steps_congruence_abs_t (t t' : term) :
  t ~>* t' -> forall k, abs_t k t ~>* abs_t k t'.
  intros. induction H; steps.
Qed.

Lemma many_steps_congruence_app_left (t t' : term) :
  t ~>* t' -> forall t1, app t t1 ~>* app t' t1.
  intros. induction H; steps.
Qed.

Lemma many_steps_congruence_app_right (t t' : term) :
  t ~>* t' -> forall t1, app t1 t ~>* app t1 t'.
  intros. induction H; steps.
Qed.

Lemma many_steps_congruence_app_t (t t' : term) :
  t ~>* t' -> forall T, app_t t T ~>* app_t t' T.
  intros. induction H; steps.
Qed.

(********************************************
 * Definitions for normal and neutral terms *
 ********************************************)

Inductive normal : term -> Prop :=
| var_normal n : normal (var n)
| abs_normal T t : normal t -> normal (abs T t)
| abs_t_normal k t : normal t -> normal (abs_t k t)
.