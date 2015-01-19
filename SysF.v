Require Import Arith.
Require Import Arith.Max.
Require Import Omega.
Require Import Lt.
Require Import Bool.

Add LoadPath ".".
Definition kind := nat.

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

Inductive env : Set :=
| empty : env
| evar  : typ -> env -> env
| etvar : kind -> env -> env
.

Fixpoint get_kind (e : env) (i : nat) : option kind :=
  match e with
    | empty => None
    | evar _ e' => get_kind e' i
    | etvar k e' =>
      if beq_nat i 0
      then Some k
      else get_kind e' (i - 1)
  end.

Fixpoint get_typ (e : env) (i : nat) : option typ :=
  match e with
    | empty => None
    | etvar _ e' => get_typ e' i
    | evar t e' =>
      if beq_nat i 0
      then Some t
      else get_typ e' (i - 1)
  end.

Fixpoint bwf_typ (e : env) (t : typ) : bool :=
  match t with
    | tvar x =>
      match get_kind e x with
        | None => false
        | Some _ => true
      end
    | tarr t1 t2 => (bwf_typ e t1 && bwf_typ e t2)%bool
    | tall k t2 => bwf_typ (etvar k e) t2
  end.

Open Scope bool.

Fixpoint bwf_env (e : env) : bool :=
  match e with
    | empty => true
    | evar t e => bwf_typ e t && bwf_env e
    | etvar k e => bwf_env e
  end.

Definition wf_typ (e : env) (t : typ) : Prop :=
  bwf_typ e t = true.

Definition wf_env (e : env) : Prop :=
  bwf_env e = true.

Fixpoint kinding (e : env) (t : typ) (k : kind) : Prop :=
  match t with
    | tvar x =>
      match get_kind e x with
        | None => False
        | Some k' => wf_env e /\ k' <= k
      end
    | tarr t1 t2 =>
      exists k1 k2 : kind,
        max k1 k2 = k /\
        kinding e t1 k1 /\
        kinding e t2 k2
    | tall k1 t1 =>
      exists k' : kind,
        kinding (etvar k1 e) t1 k' /\
        k = 1 + max k' k1
  end.

Fixpoint typing (e : env) (t : term) (ty : typ) : Prop :=
  match t with
    | var x =>
      match get_typ e x with
        | None => False
        | Some ty' => wf_env e /\ ty = ty'
      end
    | abs ty' t' =>
      match ty with
        | tarr ty1 ty2 =>
          ty1 = ty' /\
          typing (evar ty1 e) t' ty2
        | _ => False
      end
    | app t1 t2 =>
      exists ty2 : typ,
        typing e t1 (tarr ty2 ty) /\
        typing e t2 ty2
    | abs_t k t' =>
      match ty with
        | tall k' ty' =>
          k' = k /\
          typing (etvar k e) t' ty'
        | _ => False
      end
    | app_t t' ty' =>
      exists l : kind,
        exists ty1 : typ,
          typing e t' (tall l ty1) /\
          kinding e ty' l /\
          ty = tsubst ty1 0 ty'
  end.


Fixpoint kind_of (e : env) (t : typ) : option kind :=
  match t with
    | tvar x => if bwf_env e then get_kind e x else None
    | tarr t1 t2 =>
      match kind_of e t1 with
        | None => None
        | Some k1 =>
          match kind_of e t2 with
            | None => None
            | Some k2 => Some (max k1 k2)
          end
      end
    | tall k t' =>
      match kind_of (etvar k e) t' with
        | None => None
        | Some k' => Some (1 + max k k')
      end
  end.

Fixpoint beq_typ (t1 : typ) (t2 : typ) : bool :=
  match (t1, t2) with
    | (tvar x, tvar y) => beq_nat x y
    | (tarr t1 t2, tarr t1' t2') =>
      (beq_typ t1 t1' && beq_typ t2 t2')%bool
    | (tall k t, tall k' t') =>
      (beq_nat k k' && beq_typ t t')%bool
    | _ => false
  end.

Fixpoint leq (m : nat) (n : nat) :=
  match (m, n) with
    | (O, _) => true
    | (S m', S n') => leq m' n'
    | (S _, O) => false
  end.

Fixpoint type_of (e : env) (t : term) : option typ :=
  match t with
    | var x => if bwf_env e then get_typ e x else None
    | abs ty t' =>
      match type_of (evar ty e) t' with
        | Some ty1 => Some (tarr ty ty1)
        | None => None
      end
    | app t1 t2 =>
      match type_of e t1 with
        | Some (tarr ty1 ty2) =>
          match type_of e t2 with
            | Some ty1' =>
              if beq_typ ty1 ty1'
              then Some ty2
              else None
            | _ => None
          end
        | _ => None
      end
    | abs_t k t' =>
      match type_of (etvar k e) t' with
        | Some ty1 => Some (tall k ty1)
        | None => None
      end
    | app_t t ty =>
      match type_of e t with
        | Some (tall k t') =>
          match kind_of e ty with
            | Some k' =>
              if leq k' k
              then Some (tsubst t' 0 ty)
              else None
            | None => None
          end
        | _ => None
      end
  end.
