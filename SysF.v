Require Import Arith.

(** A kind is entirely defined by its level in the kind hierarchy. *)
Definition kind := nat.

(** Inductive definition of types. *)
Inductive typ :=
| tvar : nat -> typ
| tarr : typ -> typ -> typ
| tall : kind -> typ -> typ
.

(** Inductive definition of terms. *)
Inductive term :=
| var   : nat -> term
| abs   : typ -> term -> term
| app   : term -> term -> term
| abs_t : kind -> term -> term
| app_t : term -> typ -> term
.

(** [tshift X T] shifts by one the de Bruijn index of all type
    variables in type [T] with index greater than or equal to
    [X] at the current level. *)
Fixpoint tshift (X : nat) (T : typ) {struct T} : typ :=
  match T with
  | tvar Y     => tvar (if le_gt_dec X Y then S Y else Y)
  | tarr T1 T2 => tarr (tshift X T1) (tshift X T2)
  | tall K T0  => tall K (tshift (S X) T0)
  end.

(** [shift x t] shifts by one the de Bruijn index of all term
    variables in term [t] with index greater than or equal to
    [x] at the current level. *)
Fixpoint shift (x : nat) (t : term) {struct t} : term :=
  match t with
  | var y      => var (if le_gt_dec x y then S y else y)
  | abs T t0   => abs T (shift (S x) t0)
  | app t1 t2  => app (shift x t1) (shift x t2)
  | abs_t K t0 => abs_t K (shift x t0)
  | app_t t0 T => app_t (shift x t0) T
  end.

(** [shift_typ X t] shifts by one the de Bruijn index of all
    type variables in every type present in the term [t] with
    index greater than or equal to [X] at the current level. *)
Fixpoint shift_typ (X : nat) (t : term) {struct t} : term :=
  match t with
  | var y      => var y
  | abs T t0   => abs (tshift X T) (shift_typ X t0)
  | app t1 t2  => app (shift_typ X t1) (shift_typ X t2)
  | abs_t K t0 => abs_t K (shift_typ (S X) t0)
  | app_t t0 T => app_t (shift_typ X t0) (tshift X T)
  end.

(** [tsubst T X T'] replaces occurrences of the type variable
    of de Bruijn index [X] in the type [T] by the type [T'] and
    decreases by one the index of all type variables of greater
    index. *)
Fixpoint tsubst (T : typ) (X : nat) (T' : typ) {struct T} : typ :=
  match T with
  | tvar Y =>
      match lt_eq_lt_dec Y X with
      | inleft (left _)  => tvar Y
      | inleft (right _) => T'
      | inright _        => tvar (Y - 1)
      end
  | tarr T1 T2 => tarr (tsubst T1 X T') (tsubst T2 X T')
  | tall K T0  => tall K (tsubst T0 (S X) (tshift 0 T'))
  end.

(** [subst t x t'] replaces occurrences of the variable of de Bruijn
    index [x] in the term [t] by the term [t'] and decreases by one
    the index of all variables of greater index. *)
Fixpoint subst (t : term) (x : nat) (t' : term) {struct t} : term :=
  match t with
  | var y =>
      match lt_eq_lt_dec y x with
      | inleft (left _)  => var y
      | inleft (right _) => t'
      | inright _        => var (y - 1)
      end
  | abs T t0   => abs T (subst t0 (S x) (shift 0 t'))
  | app t1 t2  => app (subst t1 x t') (subst t2 x t')
  | abs_t K t0 => abs_t K (subst t0 x (shift_typ 0 t'))
  | app_t t0 T => app_t (subst t0 x t') T
  end.

(** [subst_typ t X T] replaces occurrences of the type variable of de
    Bruijn index [X] in the term [t] by the type [T] and decreases by
    one the index of all type variables of greater index. *)
Fixpoint subst_typ (t : term) (X : nat) (T : typ) {struct t} : term :=
  match t with
  | var y       => var y
  | abs T0 t0   => abs (tsubst T0 X T) (subst_typ t0 X T)
  | app t1 t2   => app (subst_typ t1 X T) (subst_typ t2 X T)
  | abs_t K t0  => abs_t K (subst_typ t0 (S X) (tshift 0 T))
  | app_t t0 T0 => app_t (subst_typ t0 X T) (tsubst T0 X T)
  end.

(** Inductive definition of environments. *)
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

(** [get_kind e i] returns the [i]-th kind in environment [e],x if it
    exists. *)
Fixpoint get_kind (e : env) (i : nat) : option kind :=
  match e with
    | empty      => None
    | evar _ e'  => get_kind e' i
    | etvar K e' =>
      match i with
        | 0    => Some K
        | S i' => get_kind e' i'
      end
  end.

(** [get_typ e i] returns the [i]-th type in environment [e], if it
    exists . *)
Fixpoint get_typ (e : env) (i : nat) : option typ :=
  match e with
    | empty => None
    | etvar _ e' => fmap (tshift 0) (get_typ e' i)
    | evar T e' =>
      match i with
        | 0    => Some T
        | S i' => get_typ e' i'
      end
  end.

Open Scope bool.

Fixpoint bwf_typ (e : env) (T : typ) : bool :=
  match T with
    | tvar X =>
      match get_kind e X with
        | None => false
        | Some _ => true
      end
    | tarr T1 T2 => bwf_typ e T1 && bwf_typ e T2
    | tall K T0 => bwf_typ (etvar K e) T0
  end.

Fixpoint bwf_env (e : env) : bool :=
  match e with
    | empty      => true
    | evar T e'  => bwf_typ e' T && bwf_env e'
    | etvar _ e' => bwf_env e'
  end.

Fixpoint wf_typ (e : env) (T : typ) : Prop :=
  match T with
    | tvar X     => get_kind e X <> None
    | tarr T1 T2 => wf_typ e T1 /\ wf_typ e T2
    | tall K T0  => wf_typ (etvar K e) T0
  end.

Fixpoint wf_env (e : env) : Prop :=
  match e with
    | empty      => True
    | evar T e'  => wf_typ e' T /\ wf_env e'
    | etvar K e' => wf_env e'
  end.

Inductive kinding : env -> typ -> kind -> Prop :=
| k_tvar (e : env) (X : nat) (Kp Kq : kind) :
      wf_env e ->
      get_kind e X = Some Kp ->
      Kp <= Kq ->
      kinding e (tvar X) Kq
| k_tall (e : env) (T : typ) (Kp Kq : kind) :
      kinding (etvar Kq e) T Kp ->
      kinding e (tall Kq T) (S (max Kp Kq))
| k_tarr (e : env) (T1 T2 : typ) (Kp Kq : kind) :
      kinding e T1 Kp ->
      kinding e T2 Kq ->
      kinding e (tarr T1 T2) (max Kp Kq)
.

Inductive typing : env -> term -> typ -> Prop :=
| t_var (e : env) (X : nat) (T : typ) :
    wf_env e ->
    get_typ e X = Some T ->
    typing e (var X) T
| t_abs (e : env) (T1 T2 : typ) (t : term) :
    wf_typ e T1 ->
    typing (evar T1 e) t T2 ->
    typing e (abs T1 t) (tarr T1 T2)
| t_app (e : env) (T1 T2 : typ) (t1 : term) (t2 : term) :
    typing e t1 (tarr T1 T2) ->
    typing e t2 T1 ->
    typing e (app t1 t2) T2
| t_abs_t (e : env) (K : kind) (t : term) (T : typ) :
    typing (etvar K e) t T ->
    typing e (abs_t K t) (tall K T)
| t_app_t (e : env) (K : kind) (t : term) (T1 T2 : typ) :
    typing e t (tall K T1) ->
    kinding e T2 K ->
    typing e (app_t t T2) (tsubst T1 0 T2)
.

Fixpoint kind_of (e : env) (T : typ) : option kind :=
  match T with
    | tvar X => if bwf_env e then get_kind e X else None
    | tarr T1 T2 =>
      match kind_of e T1 with
        | None => None
        | Some K1 =>
          match kind_of e T2 with
            | None => None
            | Some K2 => Some (max K1 K2)
          end
      end
    | tall K T0 =>
      match kind_of (etvar K e) T0 with
        | None => None
        | Some K' => Some (S (max K' K))
      end
  end.

Fixpoint beq_typ (T1 : typ) (T2 : typ) : bool :=
  match (T1, T2) with
    | (tvar X, tvar Y)           => beq_nat X Y
    | (tarr T1 T2, tarr T1' T2') => beq_typ T1 T1' && beq_typ T2 T2'
    | (tall K T, tall K' T')     => beq_nat K K' && beq_typ T T'
    | _                          => false
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
    | abs T t' =>
      match type_of (evar T e) t' with
        | Some T' => if bwf_typ e T then Some (tarr T T') else None
        | None => None
      end
    | app t1 t2 =>
      match type_of e t1 with
        | Some (tarr T1 T2) =>
          match type_of e t2 with
            | Some T1' =>
              if beq_typ T1 T1'
              then Some T2
              else None
            | _ => None
          end
        | _ => None
      end
    | abs_t K t' =>
      match type_of (etvar K e) t' with
        | Some T => Some (tall K T)
        | None => None
      end
    | app_t t' T =>
      match type_of e t' with
        | Some (tall K T') =>
          match kind_of e T with
            | Some K' =>
              if leq K' K
              then Some (tsubst T' 0 T)
              else None
            | None => None
          end
        | _ => None
      end
  end.
