Require Import Arith.

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
  | tvar Y     => tvar (if le_gt_dec X Y then S Y else Y)
  | tarr T1 T2 => tarr (tshift X T1) (tshift X T2)
  | tall K T   => tall K (tshift (S X) T)
  end.

Fixpoint shift (x : nat) (t : term) {struct t} : term :=
  match t with
  | var y       => var (if le_gt_dec x y then S y else y)
  | abs T1 t2   => abs T1 (shift (S x) t2)
  | app t1 t2   => app (shift x t1) (shift x t2)
  | abs_t T1 t2 => abs_t T1 (shift x t2)
  | app_t t1 T2 => app_t (shift x t1) T2
  end.

Fixpoint shift_typ (X : nat) (t : term) {struct t} : term :=
  match t with
  | var y      => var y
  | abs T1 t2  => abs (tshift X T1) (shift_typ X t2)
  | app t1 t2  => app (shift_typ X t1) (shift_typ X t2)
  | abs_t K t2 => abs_t K (shift_typ (S X) t2)
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
  | tall K T2   => tall K (tsubst T2 (S X) (tshift 0 T'))
  end.

Fixpoint subst (t : term) (x : nat) (t' : term) {struct t} : term :=
  match t with
  | var y =>
      match lt_eq_lt_dec y x with
      | inleft (left _)  => var y
      | inleft (right _) => t'
      | inright _        => var (y - 1)
      end
  | abs T1 t2  => abs T1 (subst t2 (S x) (shift 0 t'))
  | app t1 t2  => app (subst t1 x t') (subst t2 x t')
  | abs_t T1 t2 => abs_t T1 (subst t2 x (shift_typ 0 t'))
  | app_t t1 T2 => app_t (subst t1 x t') T2
  end.

Fixpoint subst_typ (t : term) (X : nat) (T : typ) {struct t} : term :=
  match t with
  | var y      => var y
  | abs T1 t2  => abs (tsubst T1 X T) (subst_typ t2 X T)
  | app e1 e2  => app (subst_typ e1 X T) (subst_typ e2 X T)
  | abs_t K e1 => abs_t K (subst_typ e1 (S X) (tshift 0 T))
  | app_t e1 T2 => app_t (subst_typ e1 X T) (tsubst T2 X T)
  end.

Inductive env : Set :=
| empty : env
| evar  : typ -> env -> env
| etvar : kind -> env -> env
.

Definition fmap {A B : Type} (f : A -> B) (a : option A) :=
  match a with
    | None => None
    | Some a => Some (f a)
  end.

Fixpoint get_kind (e : env) (i : nat) : option kind :=
  match e with
    | empty => None
    | evar _ e' => get_kind e' i
    | etvar k e' =>
      match i with
        | 0 => Some k
        | S i' => get_kind e' i'
      end
  end.

Fixpoint get_typ (e : env) (i : nat) : option typ :=
  match e with
    | empty => None
    | etvar _ e' => fmap (tshift 0) (get_typ e' i)
    | evar t e' =>
      match i with
        | 0 => Some t
        | S i' => get_typ e' i'
      end
  end.

Open Scope bool.

Fixpoint bwf_typ (e : env) (t : typ) : bool :=
  match t with
    | tvar x =>
      match get_kind e x with
        | None => false
        | Some _ => true
      end
    | tarr t1 t2 => bwf_typ e t1 && bwf_typ e t2
    | tall k t2 => bwf_typ (etvar k e) t2
  end.

Fixpoint bwf_env (e : env) : bool :=
  match e with
    | empty => true
    | evar t e => bwf_typ e t && bwf_env e
    | etvar k e => bwf_env e
  end.

Fixpoint wf_typ (e : env) (t : typ) : Prop :=
  match t with
    | tvar x => get_kind e x <> None
    | tarr t1 t2 => wf_typ e t1 /\ wf_typ e t2
    | tall k t2 => wf_typ (etvar k e) t2
  end.

Fixpoint wf_env (e : env) : Prop :=
  match e with
    | empty => True
    | evar t e => wf_typ e t /\ wf_env e
    | etvar k e => wf_env e
  end.

Inductive kinding : env -> typ -> kind -> Prop :=
| k_tvar (e : env) (X : nat) (p q : kind) :
      wf_env e ->
      get_kind e X = Some p ->
      p <= q ->
      kinding e (tvar X) q
| k_tall (e : env) (T : typ) (p q : kind) :
      kinding (etvar q e) T p ->
      kinding e (tall q T) (S (max p q))
| k_tarr (e : env) (T1 T2 : typ) (p q : kind) :
      kinding e T1 p ->
      kinding e T2 q ->
      kinding e (tarr T1 T2) (max p q)
.

Inductive typing : env -> term -> typ -> Prop :=
| t_var (e : env) (X : nat) (t : typ) :
    wf_env e ->
    get_typ e X = Some t ->
    typing e (var X) t
| t_abs (e : env) (t t1 : typ) (T : term) :
    wf_typ e t1 ->
    typing (evar t1 e) T t ->
    typing e (abs t1 T) (tarr t1 t)
| t_app (e : env) (t t' : typ) (T1 : term) (T2 : term) :
    typing e T1 (tarr t t') ->
    typing e T2 t ->
    typing e (app T1 T2) t'
| t_abs_t (e : env) (k : kind) (T : term) (t : typ) :
    typing (etvar k e) T t ->
    typing e (abs_t k T) (tall k t)
| t_app_t (e : env) (k : kind) (T : term) (t1 t2 : typ) :
    typing e T (tall k t1) ->
    kinding e t2 k ->
    typing e (app_t T t2) (tsubst t1 0 t2)
.
            
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
        | Some k' => Some (S (max k' k))
      end
  end.

Fixpoint beq_typ (t1 : typ) (t2 : typ) : bool :=
  match (t1, t2) with
    | (tvar x, tvar y) => beq_nat x y
    | (tarr t1 t2, tarr t1' t2') => beq_typ t1 t1' && beq_typ t2 t2'
    | (tall k t, tall k' t') => beq_nat k k' && beq_typ t t'
    | _ => false
  end.

Fixpoint type_of (e : env) (t : term) : option typ :=
  match t with
    | var x => if bwf_env e then get_typ e x else None
    | abs ty t' =>
      match type_of (evar ty e) t' with
        | Some ty1 => if bwf_typ e ty then Some (tarr ty ty1) else None
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
              if leb k' k
              then Some (tsubst t' 0 ty)
              else None
            | None => None
          end
        | _ => None
      end
  end.