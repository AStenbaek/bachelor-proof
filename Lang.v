Require Export ZArith.BinIntDef.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Lists.List.
From BSC Require Export Replace.

Module Lang.
Import Z.
Local Open Scope Z.
Definition id := nat.

(* Types *)
Inductive ty : Type :=
| Ty_Unit : ty               (* Unit *)
| Ty_Bool : ty               (* Boolean *)
| Ty_Int : ty                (* Integer *)
| Ty_Prod : ty -> ty -> ty   (* Product *)
| Ty_Sum : ty -> ty -> ty    (* Sum *)
| Ty_Arrow : ty -> ty -> ty  (* Function *)
| Ty_Var : id -> ty          (* Type Variable *)
| Ty_Forall : ty -> ty       (* Universal Type *)
| Ty_Some : ty -> ty         (* Existential Type *)
| Ty_Rec : ty -> ty          (* Recursive Type *)
| Ty_Ref : ty -> ty          (* Reference Type *).

Definition context := list ty.
Definition empty : list ty := nil.

(* Binary Operators  *)
Inductive bop : Type :=
| Op_Add : bop  (* Addition "+" *) 
| Op_Mult : bop (* Multiplication "*" *)
| Op_Sub : bop  (* Substraction "-" *)
| Op_Lt : bop   (* Less-Than "<" *)
| Op_Eq : bop   (* Equal "=" *).

(* Typing of Binary Operators  *)
Definition bop_ty bop : ty :=
  match bop with
  | Op_Add | Op_Mult | Op_Sub => Ty_Arrow (Ty_Prod Ty_Int Ty_Int) Ty_Int
  | Op_Lt | Op_Eq => Ty_Arrow (Ty_Prod Ty_Int Ty_Int) Ty_Bool
  end.

(* Expressions *)
Inductive expr : Type :=
(* Unit *)
| e_unit : expr
(* Booleans *)
| e_true : expr
| e_false : expr
| e_if : expr -> expr -> expr -> expr
(* Arithmetic *)
| e_const : Z -> expr
| e_binop : bop -> expr -> expr -> expr
(* Pairs *)
| e_pair : expr -> expr -> expr
| e_fst : expr -> expr
| e_snd : expr -> expr
(* Sums *)
| e_inl : expr -> expr
| e_inr : expr -> expr
| e_case : expr -> expr -> expr -> expr
(* STLC with recursion *)
| e_var : id -> expr
| e_app : expr -> expr -> expr
| e_rec :  expr -> expr
(* Polymorphism *)
| e_tapp : expr -> expr
| e_tabs : expr -> expr
(* Existentials *)
| e_pack : expr -> expr
| e_unpack : expr -> expr -> expr
(* Recursive Types *)
| e_fold : expr -> expr
| e_unfold : expr -> expr
(* References *)
| e_loc : nat -> expr
| e_alloc : expr -> expr
| e_assign : expr -> expr -> expr
| e_load : expr -> expr.

Global Hint Constructors expr : core.

(* Computation of binary expressions  *)
Definition compute_bop (op : bop) (i j : Z) : expr :=
  match op with
  | Op_Add => e_const (i + j)
  | Op_Mult => e_const (i * j)
  | Op_Sub => e_const (i - j)
  | Op_Lt => if (i <? j) then e_true else e_false
  | Op_Eq => if (i =? j) then e_true else e_false
  end.

(* Values *)
Inductive value : expr -> Prop :=
| v_unit : value e_unit
| v_int : forall i, value (e_const i)
| v_true : value e_true
| v_false : value e_false
| v_pair : forall v0 v1, value v0 -> value v1 -> value (e_pair v0 v1)
| v_inl : forall v, value v -> value (e_inl v)
| v_inr : forall v, value v -> value (e_inr v)
| v_rec : forall e, value (e_rec e)
| v_tabs : forall e, value (e_tabs e)
| v_pack : forall v, value v -> value (e_pack v)
| v_fold : forall v, value v -> value (e_fold v)
| v_loc : forall l, value (e_loc l).

Global Hint Constructors value : core.

Local Open Scope nat.

(* shift d from c in type T *)
Fixpoint tshift (d : id) (c : id) (T : ty) : ty :=
  match T with
  | Ty_Unit => Ty_Unit
  | Ty_Bool => Ty_Bool
  | Ty_Int => Ty_Int
  | Ty_Prod T1 T2 => Ty_Prod (tshift d c T1) (tshift d c T2)
  | Ty_Sum T1 T2 => Ty_Sum (tshift d c T1) (tshift d c T2)
  | Ty_Arrow T1 T2 => Ty_Arrow (tshift d c T1) (tshift d c T2)
  | Ty_Var k => if (k <? c) then Ty_Var k else Ty_Var (k+d)
  | Ty_Forall T1 => Ty_Forall (tshift d (S c) T1)
  | Ty_Some T1 => Ty_Some (tshift d (S c) T1)
  | Ty_Rec T1 => Ty_Rec (tshift d (S c) T1)
  | Ty_Ref T1 => Ty_Ref (tshift d c T1)
  end.
          
(* shift d from c in expression e *)
Fixpoint shift (d : id) (c : id) (e : expr) : expr :=
  match e with
  | e_var k => if (k <? c) then e_var k else e_var (k+d)
  | e_app e0 e1 => e_app (shift d c e0) (shift d c e1)
  | e_unit => e_unit
  | e_true => e_true
  | e_false => e_false
  | e_if e0 e1 e2 => e_if (shift d c e0) (shift d c e1) (shift d c e2)
  | e_const i => e_const i
  | e_binop op e0 e1 => e_binop op (shift d c e0) (shift d c e1)
  | e_pair e0 e1 => e_pair (shift d c e0) (shift d c e1)
  | e_fst e0 => e_fst (shift d c e0)
  | e_snd e1 => e_snd (shift d c e1)
  | e_inl e0 => e_inl (shift d c e0)
  | e_inr e1 => e_inr (shift d c e1)
  | e_case e0 e1 e2 => e_case (shift d c e0)
                              (shift d (S c) e1)
                              (shift d (S c) e2)
  | e_rec e0 => e_rec (shift d (S (S c)) e0)
  | e_tapp e0 => e_tapp (shift d c e0)
  | e_tabs e0 => e_tabs (shift d c e0)
  | e_pack e0 => e_pack (shift d c e0)
  | e_unpack e0 e1 => e_unpack (shift d c e0) (shift d (S c) e1)
  | e_fold e0 => e_fold (shift d c e0)
  | e_unfold e0 => e_unfold (shift d c e0)
  | e_loc l => e_loc l
  | e_alloc e0 => e_alloc (shift d c e0)
  | e_assign e0 e1 => e_assign (shift d c e0) (shift d c e1)
  | e_load e0 => e_load (shift d c e0)
  end.

(* Substitute j with X in type T
 * Worth noting: In the Ty_Var case the double conditional
 *               circumvents the need to shift -1.
 *)
Fixpoint tsubst (j : id) (X : ty) (T : ty) : ty :=
  match T with
  | Ty_Unit => Ty_Unit
  | Ty_Bool => Ty_Bool
  | Ty_Int => Ty_Int
  | Ty_Prod T1 T2 => Ty_Prod (tsubst j X T1) (tsubst j X T2)
  | Ty_Sum T1 T2 => Ty_Sum (tsubst j X T1) (tsubst j X T2)
  | Ty_Arrow T1 T2 => Ty_Arrow (tsubst j X T1) (tsubst j X T2)
  | Ty_Var k => if (k =? j) then X else (if (k <? j) then T else Ty_Var (k-1))
  | Ty_Forall T1 => Ty_Forall (tsubst (S j) (tshift 1 0 X) T1)
  | Ty_Some T1 => Ty_Some (tsubst (S j) (tshift 1 0 X) T1)
  | Ty_Rec T1 => Ty_Rec (tsubst (S j) (tshift 1 0 X) T1)
  | Ty_Ref T1 => Ty_Ref (tsubst j X T1)
  end.

(* Substitute j with s in e
 * Worth noting: In the e_var case the double conditional
 *               circumvents the need to shift -1.
 *)
Fixpoint subst (j : id) (s : expr) (e : expr) : expr :=
  match e with
  | e_var k => if (k =? j) then s else (if (k <? j) then e else e_var (k-1))
  | e_app e1 e2 => e_app (subst j s e1) (subst j s e2)
  | e_rec e1 => e_rec (subst (S (S j)) (shift 2 0 s) e1)
  | e_unit => e_unit
  | e_true => e_true
  | e_false => e_false
  | e_if e1 e2 e3 => e_if (subst j s e1) (subst j s e2) (subst j s e3)
  | e_const i => e_const i
  | e_binop bop e1 e2 => e_binop bop (subst j s e1) (subst j s e2)
  | e_pair e1 e2 => e_pair (subst j s e1) (subst j s e2)
  | e_fst e1 => e_fst (subst j s e1)
  | e_snd e2 => e_snd (subst j s e2)
  | e_inl e1 => e_inl (subst j s e1)
  | e_inr e2 => e_inr (subst j s e2)
  | e_case e1 e2 e3 => e_case (subst j s e1)
                              (subst (S j) (shift 1 0 s) e2)
                              (subst (S j) (shift 1 0 s) e3)
  | e_tapp e1 => e_tapp (subst j s e1)
  | e_tabs e1 => e_tabs (subst j s e1)
  | e_pack e1 => e_pack (subst j s e1)
  | e_unpack e1 e2 => e_unpack (subst j s e1) (subst (S j) (shift 1 0 s) e2)
  | e_fold e1 => e_fold (subst j s e1)
  | e_unfold e1 => e_unfold (subst j s e1)
  | e_loc l => e_loc l
  | e_alloc e1 => e_alloc (subst j s e1)
  | e_assign e1 e2 => e_assign (subst j s e1) (subst j s e2)
  | e_load e1 => e_load (subst j s e1)
  end.


Definition store_ty := list ty.

(* This is to make Coq more cooperative.
 * The None case does not actually appear in typing, *)
Definition store_ty_lookup (Σ : store_ty) (l : nat) :=
  match nth_error Σ l with
  | Some T => T
  | None => Ty_Unit
  end.

(* Typing Relation  *)
Inductive has_type (Σ : store_ty) : context -> expr -> ty -> Prop :=
(* STLC with recursion  *)
| T_Var : forall Γ k T,
    nth_error Γ k = Some T -> has_type Σ Γ (e_var k) T
| T_App : forall Γ T1 T2 e1 e2,
    has_type Σ Γ e1 (Ty_Arrow T2 T1) ->
    has_type Σ Γ e2 T2 ->
    has_type Σ Γ (e_app e1 e2) T1
| T_Rec : forall Γ T1 T2 e,
    has_type Σ ((Ty_Arrow T2 T1)::T2::Γ) e T1 ->
    has_type Σ Γ (e_rec e) (Ty_Arrow T2 T1)
(* Unit *)
| T_Unit : forall Γ, has_type Σ Γ e_unit Ty_Unit
(* Booleans *)
| T_True : forall Γ, has_type Σ Γ e_true Ty_Bool
| T_False : forall Γ, has_type Σ Γ e_false Ty_Bool
| T_If : forall Γ e1 e2 e3 T,
    has_type Σ Γ e1 Ty_Bool ->
    has_type Σ Γ e2 T ->
    has_type Σ Γ e3 T ->
    has_type Σ Γ (e_if e1 e2 e3) T
(* Integers and Arithmetic *)
| T_Int : forall Γ i, has_type Σ Γ (e_const i) Ty_Int
| T_Binop : forall Γ bop e1 e2 T1 T2 T3,
    bop_ty bop = Ty_Arrow (Ty_Prod T1 T2) T3 ->
    has_type Σ Γ e1 T1 ->
    has_type Σ Γ e2 T2 ->
    has_type Σ Γ (e_binop bop e1 e2) T3
(* Products *)
| T_Pair : forall Γ T1 T2 e1 e2,
    has_type Σ Γ e1 T1 ->
    has_type Σ Γ e2 T2 ->
    has_type Σ Γ (e_pair e1 e2) (Ty_Prod T1 T2)
| T_Fst : forall Γ T1 T2 e,
    has_type Σ Γ e (Ty_Prod T1 T2) ->
    has_type Σ Γ (e_fst e) T1
| T_Snd : forall Γ T1 T2 e,
    has_type Σ Γ e (Ty_Prod T1 T2) ->
    has_type Σ Γ (e_snd e) T2
(* Sums *)
| T_Inl : forall Γ T1 T2 e,
    has_type Σ Γ e T1 ->
    has_type Σ Γ (e_inl e) (Ty_Sum T1 T2)
| T_Inr : forall Γ T1 T2 e,
    has_type Σ Γ e T2 ->
    has_type Σ Γ (e_inr e) (Ty_Sum T1 T2)
| T_Case : forall Γ T1 T2 T3 e0 e1 e2,
    has_type Σ Γ e0 (Ty_Sum T1 T2) ->
    has_type Σ (T1::Γ) e1 T3 ->
    has_type Σ (T2::Γ) e2 T3 ->
    has_type Σ Γ (e_case e0 e1 e2) T3
(* Polymorphism *)
| T_Tabs : forall Γ T e,
    has_type (map (tshift 1 0) Σ) (map (tshift 1 0) Γ) e T ->
    has_type Σ Γ (e_tabs e) (Ty_Forall T) 
| T_Tapp : forall Γ T1 T2 e,
    has_type Σ Γ e (Ty_Forall T1) ->
    has_type Σ Γ (e_tapp e) (tsubst 0 T2 T1)
(* Existentials *)
| T_Pack : forall Γ T1 T2 e,
    has_type Σ Γ e (tsubst 0 T1 T2) ->
    has_type Σ Γ (e_pack e) (Ty_Some T2)
| T_Unpack : forall Γ T1 T2 e1 e2,
    has_type Σ Γ e1 (Ty_Some T1) ->
    has_type (map (tshift 1 0) Σ) (T1::(map (tshift 1 0) Γ)) e2 (tshift 1 0 T2) ->
    has_type Σ Γ (e_unpack e1 e2) T2
(* Recursives *)
| T_Fold : forall Γ T e,
    has_type Σ Γ e (tsubst 0 (Ty_Rec T) T) ->
    has_type Σ Γ (e_fold e) (Ty_Rec T)
| T_Unfold : forall Γ T e,
    has_type Σ Γ e (Ty_Rec T) ->
    has_type Σ Γ (e_unfold e) (tsubst 0 (Ty_Rec T) T)
(* References 
 * Note: l < length Σ models l ∈ dom(Σ) *)
| T_Loc : forall Γ l,
    l < length Σ ->
    has_type Σ Γ (e_loc l) (Ty_Ref (store_ty_lookup Σ l))
| T_Alloc : forall Γ T e,
    has_type Σ Γ e T ->
    has_type Σ Γ (e_alloc e) (Ty_Ref T)
| T_Assign : forall Γ T e1 e2,
    has_type Σ Γ e1 (Ty_Ref T) ->
    has_type Σ Γ e2 T ->
    has_type Σ Γ (e_assign e1 e2) (Ty_Unit)
| T_Load : forall Γ T e,
    has_type Σ Γ e (Ty_Ref T) ->
    has_type Σ Γ (e_load e) T.

Global Hint Constructors has_type : core.

Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Definition store := list expr.
Definition store_lookup (σ : store) (l : nat) :=
  match nth_error σ l with
  | Some v => v
  | None => e_unit
  end.

Reserved Notation "e '-->' e'" (at level 40).

Inductive step : store * expr -> store * expr -> Prop :=
(* Function Application *)
| ST_AppRec : forall σ e v,
    value v ->
    (σ, e_app (e_rec e) v) --> (σ, subst 0 v (subst 0 (shift 1 0 (e_rec e)) e))
| ST_App1 : forall σ σ' e1 e1' e2,
    (σ, e1) --> (σ', e1') ->
    (σ, e_app e1 e2) --> (σ', e_app e1' e2)
| ST_App2 : forall σ σ' v1 e2 e2',
    value v1 ->
    (σ, e2) --> (σ', e2') ->
    (σ, e_app v1 e2) --> (σ', e_app v1 e2')
(* Binary Operations *)
| ST_Binop1 : forall σ σ' op e1 e1' e2,
    (σ, e1) --> (σ', e1') ->
    (σ, e_binop op e1 e2) --> (σ', e_binop op e1' e2)
| ST_Binop2 : forall σ σ' op v1 e2 e2',
    value v1 ->
    (σ, e2) --> (σ', e2') ->
    (σ, e_binop op v1 e2) --> (σ', e_binop op v1 e2')
| ST_Binop3 : forall σ op v1 v2,
    (σ, e_binop op (e_const v1) (e_const v2)) --> (σ, compute_bop op v1 v2)
(* If-Then-Else  *)
| ST_If : forall σ σ' e1 e1' e2 e3,
    (σ, e1) --> (σ', e1') ->
    (σ, e_if e1 e2 e3) --> (σ', e_if e1' e2 e3)
| ST_IfTrue : forall σ e2 e3,
    (σ, e_if e_true e2 e3) --> (σ, e2)
| ST_IfFalse : forall σ e2 e3,
    (σ, e_if e_false e2 e3) --> (σ, e3)
(* Products *)
| ST_Pair1 : forall σ σ' e1 e1' e2,
    (σ, e1) --> (σ', e1') ->
    (σ, e_pair e1 e2) --> (σ', e_pair e1' e2)
| ST_Pair2 : forall σ σ' v1 e2 e2',
    value v1 ->
    (σ, e2) --> (σ', e2') ->
    (σ, e_pair v1 e2) --> (σ', e_pair v1 e2')
| ST_Fst1 : forall σ σ' e1 e1',
    (σ, e1) --> (σ', e1') ->
    (σ, e_fst e1) --> (σ', e_fst e1')
| ST_Fst2 : forall σ v1 v2,
    value v1 ->
    value v2 ->
    (σ, e_fst (e_pair v1 v2)) --> (σ, v1)
| ST_Snd1 : forall σ σ' e1 e1',
    (σ, e1) --> (σ', e1') ->
    (σ, e_snd e1) --> (σ', e_snd e1')
| ST_Snd2 : forall σ v1 v2,
    value v1 ->
    value v2 ->
    (σ, e_snd (e_pair v1 v2)) --> (σ, v2)
(* Sums *)
| ST_Inl : forall σ σ' e1 e1',
    (σ, e1) --> (σ', e1') ->
    (σ, e_inl e1) --> (σ', e_inl e1')
| ST_Inr : forall σ σ' e2 e2',
    (σ, e2) --> (σ', e2') ->
    (σ, e_inr e2) --> (σ', e_inr e2')
| ST_Case : forall σ σ' e1 e1' e2 e3,
    (σ, e1) --> (σ', e1') ->
    (σ, e_case e1 e2 e3) --> (σ', e_case e1' e2 e3)
| ST_CaseInl : forall σ v1 e2 e3,
    value v1 ->
    (σ, e_case (e_inl v1) e2 e3) --> (σ, subst 0 v1 e2)
| ST_CaseInr : forall σ v2 e2 e3,
    value v2 ->
    (σ, e_case (e_inr v2) e2 e3) --> (σ, subst 0 v2 e3)
(* Polymorphism *)
| ST_TApp : forall σ σ' e1 e1',
    (σ, e1) --> (σ', e1') ->
    (σ, e_tapp e1) --> (σ', e_tapp e1')
| ST_TAppAbs : forall σ e,
    (σ, e_tapp (e_tabs e)) --> (σ, e)
(* Existentials *)
| ST_Pack : forall σ σ' e1 e1',
    (σ, e1) --> (σ', e1') ->
    (σ, e_pack e1) --> (σ', e_pack e1')
| ST_Unpack : forall σ σ' e1 e1' e2,
    (σ, e1) --> (σ', e1') ->
    (σ, e_unpack e1 e2) --> (σ', e_unpack e1' e2)
| ST_UnpackPack : forall σ v1 e2,
    value v1 ->
    (σ, e_unpack (e_pack v1) e2) --> (σ, subst 0 v1 e2)
(* Recursives *)
| ST_UnfoldFold : forall σ v,
    value v ->
    (σ, e_unfold (e_fold v)) --> (σ, v)
| ST_Fold : forall σ σ' e e',
    (σ, e) --> (σ', e') ->
    (σ, e_fold e) --> (σ', e_fold e')
| ST_Unfold : forall σ σ' e e',
    (σ, e) --> (σ', e') ->
    (σ, e_unfold e) --> (σ', e_unfold e')
(* References *)
| ST_Alloc : forall σ σ' e e',
    (σ, e) --> (σ', e') ->
    (σ, e_alloc e) --> (σ', e_alloc e')
| ST_AllocValue : forall σ v,
    value v ->
    (σ, e_alloc v) --> (σ++(v::nil), e_loc (length σ))
| ST_Assign1 : forall σ σ' e1 e1' e2,
    (σ, e1) --> (σ', e1') ->
    (σ, e_assign e1 e2) --> (σ', e_assign e1' e2)
| ST_Assign2 : forall σ σ' v e2 e2',
    value v ->
    (σ, e2) --> (σ', e2') ->
    (σ, e_assign v e2) --> (σ', e_assign v e2')
| ST_AssignValue : forall σ l v,
    value v ->
    l < length σ ->
    (σ, e_assign (e_loc l) v) --> (replace l v σ, e_unit)
| ST_Load : forall σ σ' e e',
    (σ, e) --> (σ', e') ->
    (σ, e_load e) --> (σ', e_load e')
| ST_LoadLoc : forall σ l,
    l < length σ ->
    (σ, e_load (e_loc l)) --> (σ, store_lookup σ l)
where "e '-->' e'" := (step e e').

Notation "e '-->*' e'" := (multi step e e') (at level 40).


(** Notation Settings. **)

(* Notation is a modified version of the 
** notation found in the Sofware Foundations Programming Languages book *)
Declare Custom Entry ks.
Declare Custom Entry ks_ty.

Notation "<{ e }>" := e (e custom ks at level 99).
Notation "<{{ e }}>" := e (e custom ks_ty at level 99).
Notation "( x )" := x (in custom ks, x at level 99).
Notation "( x )" := x (in custom ks_ty, x at level 99).
Notation "x" := x (in custom ks at level 0, x constr at level 0).
Notation "x" := x (in custom ks_ty at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom ks_ty at level 50, right associativity).
Notation "x y" := (e_app x y) (in custom ks at level 1, left associativity).
Notation "'λ' , y" := (e_rec y) (in custom ks at level 90,
                                    y custom ks at level 99,
                                    left associativity).
Notation "# n" := (e_var (n%nat)) (in custom ks at level 99).
Coercion e_const : Z >-> expr.

Notation "'Int'" := Ty_Int (in custom ks_ty at level 0).
Notation "x + y" := (e_binop Op_Add x y) (in custom ks at level 1,
                                      x custom ks,
                                      y custom ks,
                                      left associativity).
Notation "x * y" := (e_binop Op_Mult x y) (in custom ks at level 1,
                                      x custom ks,
                                      y custom ks,
                                      left associativity).
Notation "x - y" := (e_binop Op_Sub x y) (in custom ks at level 1,
                                      x custom ks,
                                      y custom ks,
                                      left associativity).
Notation "x < y" := (e_binop Op_Lt x y) (in custom ks at level 1,
                                      x custom ks,
                                      y custom ks,
                                      left associativity).
Notation "x = y" := (e_binop Op_Eq x y) (in custom ks at level 1,
                                      x custom ks,
                                      y custom ks,
                                      left associativity).

Notation "S + T" := (Ty_Sum S T) (in custom ks_ty at level 3, left associativity).
Notation "'inl' e" := (e_inl e) (in custom ks at level 0,
                                        e custom ks at level 0).
Notation "'inr' e" := (e_inr e) (in custom ks at level 0,
                                        e custom ks at level 0).
Notation "'case' e0 'of' '|' 'inl' e1 '|' 'inr' e2" :=
  (e_case e0 e1 e2) (in custom ks at level 89,
                               e0 custom ks at level 99,
                               e1 custom ks at level 99,
                               e2 custom ks at level 99,
                               left associativity).

Notation "S * T" := (Ty_Prod S T) (in custom ks_ty at level 2,
                                      S custom ks_ty,
                                      T custom ks_ty at level 0).
Notation "( x ',' y )" := (e_pair x y) (in custom ks at level 0,
                                           x custom ks at level 99,
                                           y custom ks at level 99).
Notation "e '.fst'" := (e_fst e) (in custom ks at level 0).
Notation "e '.snd'" := (e_snd e) (in custom ks at level 0).

Notation "'Unit'" := (Ty_Unit) (in custom ks_ty at level 0).
Notation "'unit'" := (e_unit) (in custom ks at level 0).

Notation "'Bool'" := (Ty_Bool) (in custom ks_ty at level 0).
Notation "'true'" := (e_true) (in custom ks at level 0).
Notation "'false'" := (e_false) (in custom ks at level 0).
Notation "'if' e0 'then' e1 'else' e2" := (e_if e0 e1 e2) (in custom ks at level 89,
                                                              e0 custom ks at level 99,
                                                              e1 custom ks at level 99,
                                                              e2 custom ks at level 99).

Notation "'[' # j ':=' s ']' e" := (subst (j%nat) s e) (in custom ks at level 20).

Notation "@ n" := (Ty_Var n%nat) (in custom ks_ty at level 99).
Notation "'∀X,' T" := (Ty_Forall T) (in custom ks_ty at level 2,
                                        T custom ks_ty at level 0).
Notation "'∃X,' T" := (Ty_Some T) (in custom ks_ty at level 2,
                                      T custom ks_ty at level 0).
Notation "'[|' @ j '/' X '|]' T" := (tsubst (j%nat) X T) (in custom ks_ty at level 20).
Notation "'Λ' e" := (e_tabs e) (in custom ks at level 0,
                                 e custom ks at level 0).
Notation "e '_'" := (e_tapp e) (in custom ks at level 30).
Notation "'pack' e" := (e_pack e) (in custom ks at level 30).
Notation "'unpack' e 'in' e'" := (e_unpack e e') (in custom ks at level 89,
                                                     e custom ks at level 99,
                                                     e' custom ks at level 99).
Notation "'fold' e" := (e_fold e) (in custom ks at level 30).
Notation "'unfold' e" := (e_unfold e) (in custom ks at level 30).

End Lang.
