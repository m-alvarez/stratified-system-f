Require Import Arith.

Inductive kind :=
| star : nat -> kind
.

Inductive typ :=
| tvar : nat -> typ
| tarr : typ -> typ -> typ
| tall : kind -> typ -> typ
.

Inductive term :=
| var   : nat -> term
| abs   : typ -> term -> term
| app   : term -> term -> term
| abs_t : kind -> term -> term
| app_t : term -> typ -> term
.

Fixpoint tshift (X : nat) (T : typ) {struct T} : typ :=
  match T with
  | tvar Y     => tvar (if le_gt_dec X Y then 1 + Y else Y)
  | tarr T1 T2 => tarr (tshift X T1) (tshift X T2)
  | tall K T   => tall K (tshift (1 + X) T)
  end.

Fixpoint shift (x : nat) (t : term) {struct t} : term :=
  match t with
  | var y       => var (if le_gt_dec x y then 1 + y else y)
  | abs T1 t2   => abs T1 (shift (1 + x) t2)
  | app t1 t2   => app (shift x t1) (shift x t2)
  | abs_t T1 t2 => abs_t T1 (shift x t2)
  | app_t t1 T2 => app_t (shift x t1) T2
  end.

Fixpoint shift_typ (X : nat) (t : term) {struct t} : term :=
  match t with
  | var y      => var y
  | abs T1 t2  => abs (tshift X T1) (shift_typ X t2)
  | app t1 t2  => app (shift_typ X t1) (shift_typ X t2)
  | abs_t K t2 => abs_t K (shift_typ (1 + X) t2)
  | app_t t1 T2 => app_t (shift_typ X t1) (tshift X T2)
  end.

Fixpoint tsubst (T : typ) (X : nat) (T' : typ) {struct T} : typ :=
  match T with
  | tvar Y =>
      match lt_eq_lt_dec Y X with
      | inleft (left _)  => tvar Y
      | inleft (right _) => T'
      | inright _        => tvar (Y - 1)
      end
  | tarr T1 T2 => tarr (tsubst T1 X T') (tsubst T2 X T')
  | tall K T2   => tall K (tsubst T2 (1 + X) (tshift 0 T'))
  end.

Fixpoint subst (t : term) (x : nat) (t' : term) {struct t} : term :=
  match t with
  | var y =>
      match lt_eq_lt_dec y x with
      | inleft (left _)  => var y
      | inleft (right _) => t'
      | inright _        => var (y - 1)
      end
  | abs T1 t2  => abs T1 (subst t2 (1 + x) (shift 0 t'))
  | app t1 t2  => app (subst t1 x t') (subst t2 x t')
  | abs_t T1 t2 => abs_t T1 (subst t2 x (shift_typ 0 t'))
  | app_t t1 T2 => app_t (subst t1 x t') T2
  end.

Fixpoint subst_typ (t : term) (X : nat) (T : typ) {struct t} : term :=
  match t with
  | var y      => var y
  | abs T1 t2  => abs (tsubst T1 X T) (subst_typ t2 X T)
  | app e1 e2  => app (subst_typ e1 X T) (subst_typ e2 X T)
  | abs_t K e1 => abs_t K (subst_typ e1 (1 + X) (tshift 0 T))
  | app_t e1 T2 => app_t (subst_typ e1 X T) (tsubst T2 X T)
  end.

Definition env : Set :=
| 