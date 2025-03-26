-- import Ssreflect.Lang
import Mathlib.Data.Finmap
import Mathlib.Data.Real.Basic

import SPLean.Common.Util
import SPLean.Common.Heap


open Classical

/- =========================== Language Syntax =========================== -/

inductive prim where
  -- | val_ref : prim
  | val_get : prim
  | val_set : prim
  -- | val_free : prim
  | val_neg : prim
  | val_opp : prim
  | val_eq : prim
  | val_add : prim
  | val_neq : prim
  | val_sub : prim
  | val_mul : prim
  | val_div : prim
  | val_mod : prim
  -- | val_rand : prim
  | val_le : prim
  | val_lt : prim
  | val_ge : prim
  | val_gt : prim
  | val_ptr_add : prim


def null : loc := 0

mutual
  inductive val : Type where
    | val_unit   : val
    | val_bool   : Bool → val
    | val_int    : Int → val
    | val_real   : ℝ → val
    | val_loc    : loc → val
    | val_prim   : prim → val
    | val_fun    : var -> trm -> val
    | val_fix    : var -> var -> trm -> val
    | val_uninit : val
    | val_error : val
    -- | val_alloc : val
    -- | val_array_make : val
    -- | val_array_length : val
    -- | val_array_get : val
    -- | val_array_set : val

  inductive trm : Type where
    | trm_val   : val -> trm
    | trm_var   : var -> trm
    | trm_fun   : var -> trm -> trm
    | trm_fix   : var -> var -> trm -> trm
    | trm_app   : trm -> trm -> trm
    | trm_seq   : trm -> trm -> trm
    | trm_let   : var -> trm -> trm -> trm
    | trm_if    : trm -> trm -> trm -> trm
    | trm_for   : var -> trm -> trm -> trm -> trm
    | trm_while : trm -> trm -> trm
    | trm_ref   : var → trm → trm → trm
    | trm_alloc : var → trm → trm → trm
end

/- States and heaps are represented as finite maps -/
abbrev state := Finmap (λ _ : loc ↦ val)
abbrev heap := Heap.heap val

section
/- ============================= Notations ============================= -/

/- val and term are inhabited -/
instance : Inhabited val where
  default := val.val_unit

instance : Inhabited trm where
  default := trm.trm_val (val.val_unit)

/- Coercions -/
instance : Coe Bool val where
  coe b := val.val_bool b

instance : Coe Int val where
  coe z := val.val_int z

/- Help Lean to treat Nat as val -/
instance : OfNat val n where
  ofNat := val.val_int n

instance : Coe loc val where
  coe l := val.val_loc l

instance : Coe prim val where
  coe x := val.val_prim x

instance : Coe val trm where
  coe v := trm.trm_val v

instance : Coe var trm where
  coe x := trm.trm_var x

instance : CoeFun trm (fun _ => trm -> trm) where
  coe x := trm.trm_app x

/- ================== Terms, Values and Substitutions ================== -/
open trm

abbrev trm_is_val : trm → Prop
  | trm_val _ => true
  | _         => false

/- Capture-avoiding substitution -/
def subst (y : var) (v' : val) (t : trm) : trm :=
  -- let aux x := subst y v' x
  let if_y_eq x t1 t2 := if x = y then t1 else t2
  match t with
  | trm_val v          => trm_val v
  | trm_var x          => if_y_eq x (trm_val v') t
  | trm_fun x t1       => trm_fun x (if_y_eq x t1 (subst y v' t1))
  | trm_fix f x t1     => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (subst y v' t1)))
  | trm_app t1 t2      => trm_app (subst y v' t1) (subst y v' t2)
  | trm_seq t1 t2      => trm_seq (subst y v' t1) (subst y v' t2)
  | trm_let x t1 t2    => trm_let x (subst y v' t1) (if_y_eq x t2 (subst y v' t2))
  | trm_if t0 t1 t2    => trm_if (subst y v' t0) (subst y v' t1) (subst y v' t2)
  | trm_for x t1 t2 t3 => trm_for x (subst y v' t1) (subst y v' t2) (if_y_eq x t3 (subst y v' t3))
  | trm_while t1 t2    => trm_while (subst y v' t1) (subst y v' t2)
  | trm_ref x t1 t2    => trm_ref x (subst y v' t1) (if_y_eq x t2 (subst y v' t2))
  | trm_alloc x t1 t2  => trm_alloc x (subst y v' t1) (if_y_eq x t2 (subst y v' t2))

noncomputable def is_true (P : Prop) : Bool :=
  if P then true else false


/- ======================= Small-Step Semantics ======================= -/
open val
open prim

/- Function for reading a memory location (to unwrap the option) -/
def read_state (p : loc) (h : state) :=
  match Finmap.lookup p h with
  | some v => v
  | none   => default

inductive step : state → trm → state → trm → Prop where

  -- Context Rules
  | step_seq_ctx : forall s1 s2 t1 t1' t2,
      step s1 t1 s2 t1' →
      step s1 (trm_seq t1 t2) s2 (trm_seq t1' t2)
  | step_let_ctx : forall s1 s2 x t1 t1' t2,
      step s1 t1 s2 t1' →
      step s1 (trm_let x t1 t2) s2 (trm_let x t1' t2)
  | step_app_arg_1 : forall s1 s2 t1 t1' t2,
      step s1 t1 s2 t1' →
      step s1 (trm_app t1 t2) s2 (trm_app t1' t2)
  | step_app_arg2 : forall s1 s2 v1 t2 t2',
      step s1 t2 s2 t2' →
      step s1 (trm_app v1 t2) s2 (trm_app v1 t2')

  -- Reduction
  | step_fun : forall s x t1,
      step s (trm_fun x t1) s (val_fun x t1)
  | step_fix : forall s f x t1,
      step s (trm_fix f x t1) s (val_fix f x t1)
  | step_app_fun : forall s v1 v2 x t1,
      v1 = val_fun x t1 →
      v2 = trm_val v2' →
      step s (trm_app v1 v2) s (subst x v2' t1)
  | step_app_fix : forall s v1 v2 f x t1,
      v1 = val_fix f x t1 →
      v2 = trm_val v2' →
      step s (trm_app v1 v2) s (subst x v2' (subst f v1 t1))
  | step_if : forall s b t1 t2,
      step s (trm_if (val_bool b) t1 t2) s (if b then t1 else t2)
  | step_seq : forall s t2 v1,
      step s (trm_seq v1 t2) s t2
  | step_let : forall s x t2 v1,
      v1 = trm_val v1' →
      step s (trm_let x v1 t2) s (subst x v1' t2)

  -- Theories Operations
  | step_neg : forall s b,
      step s (trm_app val_neg (val_bool b)) s (val_bool (¬ b))
  | step_opp : forall s n,
      step s (trm_app val_opp (val_int n)) s (val_int (- n))
  -- | step_rand : forall s n n1,
  --     0 <= n1 ∧ n1 < n →
  --     step s (trm_app val_rand (val_int n)) s (val_int n1)

  -- Binary Operations
  | step_eq : forall s v1 v2,
      step s (trm_app (trm_app val_eq v1) v2) s (val_bool (is_true (v1 = v2)))
  | step_neq : forall s v1 v2,
      step s (trm_app (trm_app val_neq v1) v2) s (val_bool (is_true (v1 ≠ v2)))
  | step_add : forall s n1 n2,
      step s (trm_app (trm_app val_add (val_int n1)) (val_int n2)) s
        (val_int (n1 + n2))
  | step_sub : forall s n1 n2,
      step s (trm_app (trm_app val_sub (val_int n1)) (val_int n2)) s
        (val_int (n1 - n2))
  | step_mul : forall s n1 n2,
      step s (trm_app (trm_app val_mul (val_int n1)) (val_int n2)) s
        (val_int (n1 * n2))
  | step_div : forall s n1 n2,
      n2 ≠ 0 →
      step s (trm_app (trm_app val_div (val_int n1)) (val_int n2)) s
        (n1 / n2)
  | step_mod : forall s n1 n2,
      n2 ≠ 0 →
      step s (trm_app (trm_app val_mod (val_int n1)) (val_int n2)) s
        (n1 % n2)
  | step_le : forall s n1 n2,
      step s (trm_app (trm_app val_le (val_int n1)) (val_int n2)) s
        (val_bool (n1 <= n2))
  | step_lt : forall s n1 n2,
      step s (trm_app (trm_app val_lt (val_int n1)) (val_int n2)) s
        (val_bool (n1 < n2))
  | step_ge : forall s n1 n2,
      step s (trm_app (trm_app val_ge (val_int n1)) (val_int n2)) s
        (val_bool (n1 >= n2))
  | step_gt : forall s n1 n2,
      step s (trm_app (trm_app val_gt (val_int n1)) (val_int n2)) s
        (val_bool (n1 > n2))
  | step_ptr_add : forall s p1 p2 n,
      (p2:ℤ) = (p1:loc) + n →
      step s (trm_app (trm_app val_ptr_add (val_loc p1)) (val_int n)) s
        (val_loc (Int.toNat p2))

  -- Heap Opeartions
  | step_ref : forall s v p,
      ¬ p ∈ s →
      v = trm_val v' →
      step s (trm_app val_ref v) (Finmap.insert p v' s) (val_loc p)
  | step_get : forall s p,
      p ∈ s →
      step s (trm_app val_get (val_loc p)) s (read_state p s)
  | step_set : forall s p v,
      p ∈ s ->
      v = trm_val v' →
      step s (trm_app (trm_app val_set (val_loc p)) v)
        (Finmap.insert p v' s) val_unit
  | step_free : forall s p,
      p ∈ s →
      step s (trm_app val_free (val_loc p)) (Finmap.erase p s) val_unit

/- Multi-step relation -/
inductive steps : state → trm → state → trm → Prop :=
  | steps_refl : forall s t,
      steps s t s t
  | steps_step : forall s1 s2 s3 t1 t2 t3,
      step s1 t1 s2 t2 →
      steps s2 t2 s3 t3 →
      steps s1 t1 s3 t3

lemma steps_of_step s1 s2 t1 t2 :
  step s1 t1 s2 t2 → steps s1 t1 s2 t2 :=
by
  sby move=> ?; apply steps.steps_step

lemma steps_trans s1 s2 s3 t1 t2 t3 :
  steps s1 t1 s2 t2 →
  steps s2 t2 s3 t3 →
  steps s1 t1 s3 t3 := by sby elim

/- Predicate [reducible s t] for asserting that [(s, t)] can step -/
def reducible (s : state) (t : trm) : Prop :=
  exists s' t', step s t s' t'

/- The configuration [(s, t)] is not stuck, i.e. [notstuck s t] if either
   t is a value or [(s, t)] can step -/
def notstuck (s : state) (t : trm) : Prop :=
  trm_is_val t \/ reducible s t


/- ========== Big-step Semantics for Primitive Operations ========== -/

/- Big-step relation for Theories operators -/
inductive evalunop : prim → val → (val → Prop) → Prop where
  | evalunop_neg : forall b1,
      evalunop val_neg (val_bool b1) (fun v => v = val_bool (¬ b1))
  | evalunop_opp : forall n1,
      evalunop val_opp (val_int n1) (fun v => v = val_int (- n1))
  | evalunop_oppr : forall r1,
      evalunop val_opp (val_real r1) (fun v => v = val_real (- r1))
  -- | evalunop_rand : forall n,
  --     n > 0 →
  --     evalunop val_rand (val_int n)
  --       (fun r => exists n1, r = val_int n1 ∧ 0 <= n1 ∧ n1 < n)

/- Big-step relation for binary operators -/
inductive evalbinop : val → val → val → (val->Prop) → Prop where
  | evalbinop_eq : forall v1 v2,
      evalbinop val_eq v1 v2 (fun v => v = val_bool (is_true (v1 = v2)))
  | evalbinop_neq : forall v1 v2,
      evalbinop val_neq v1 v2 (fun v => v = val_bool (is_true (v1 ≠ v2)))
  | evalbinop_add : forall n1 n2,
      evalbinop val_add (val_int n1) (val_int n2)
        (fun v => v = val_int (n1 + n2))
  | evalbinop_addr : forall r₁ r₂,
      evalbinop val_add (val_real r₁) (val_real r₂)
        (fun v => v = val_real (r₁ + r₂))
  | evalbinop_sub : forall n1 n2,
      evalbinop val_sub (val_int n1) (val_int n2)
        (fun v => v = val_int (n1 - n2))
  | evalbinop_subr : forall r1 r2,
      evalbinop val_sub (val_real r1) (val_real r2)
        (fun v => v = val_real (r1 - r2))
  | evalbinop_mul : forall n1 n2,
      evalbinop val_mul (val_int n1) (val_int n2)
        (fun v => v = val_int (n1 * n2))
  | evalbinop_mulr : forall r1 r2,
      evalbinop val_mul (val_real r1) (val_real r2)
        (fun v => v = val_real (r1 * r2))
  | evalbinop_div : forall n1 n2,
      ¬(n2 = 0) →
      evalbinop val_div (val_int n1) (val_int n2)
        (fun v => v = val_int (n1 / n2))
  | evalbinop_divr : forall r1 r2,
      ¬(r2 = 0) →
      evalbinop val_div (val_real r1) (val_real r2)
        (fun v => v = val_real (r1 / r2))
  | evalbinop_mod : forall n1 n2,
      ¬(n2 = 0) →
      evalbinop val_mod (val_int n1) (val_int n2)
        (fun v => v = val_int (n1 % n2))
  | evalbinop_le : forall n1 n2,
      evalbinop val_le (val_int n1) (val_int n2)
        (fun v => v = val_bool (n1 <= n2))
  | evalbinop_ler : forall r1 r2,
      evalbinop val_le (val_real r1) (val_real r2)
        (fun v => v = val_bool (r1 <= r2))
  | evalbinop_lt : forall n1 n2,
      evalbinop val_lt (val_int n1) (val_int n2)
        (fun v => v = val_bool (n1 < n2))
  | evalbinop_ltr : forall r1 r2,
      evalbinop val_lt (val_real r1) (val_real r2)
        (fun v => v = val_bool (r1 < r2))
  | evalbinop_ge : forall n1 n2,
      evalbinop val_ge (val_int n1) (val_int n2)
        (fun v => v = val_bool (n1 >= n2))
  | evalbinop_ger : forall r1 r2,
      evalbinop val_ge (val_real r1) (val_real r2)
        (fun v => v = val_bool (r1 >= r2))
  | evalbinop_gt : forall n1 n2,
      evalbinop val_gt (val_int n1) (val_int n2)
        (fun v => v = val_bool (n1 > n2))
  | evalbinop_gtr : forall r1 r2,
      evalbinop val_gt (val_real r1) (val_real r2)
        (fun v => v = val_bool (r1 > r2))

  -- Not really sure what's going on in the last rule here since
  -- in the original CFML code, p2 doesn't have to be a valid pointer (it has
  -- type int and could be negative), so not sure if this is semantically
  -- equivalent to what was here before.
  | evalbinop_ptr_add : forall (p1 : loc) (p2 : Int) n,
      p2 = p1 + n ->
      evalbinop val_ptr_add (val_loc p1) (val_int n)
        (fun v => v = val_loc (Int.natAbs p2))

lemma evalunop_unique :
  evalunop op v P → evalunop op v P' → P = P' := by
  elim=> >
  { sby move=> [] }
  { sby move=> [] }
  { sby move=> [] }
  -- { sby move=> ? [] }

lemma evalbinop_unique :
  evalbinop op v1 v2 P → evalbinop op v1 v2 P' → P = P' := by
  elim=> >
  any_goals (sby move=> [])
  all_goals (sby move=> ? [])


/- ========================= Big-step Semantics ========================= -/

section eval

/- Predicate for converting predicates [P : val → Prop] into postconditions
   of type [val → state → Prop] that hold in state s -/
def purepost (s : state) (P : val → Prop) : val → state → Prop :=
  fun v s' => P v ∧ s' = s

def purepostin (s : state) (P : val → Prop) (Q : val → state → Prop) : Prop :=
  -- Equivalent to [purepost S P ===> Q]
  forall v, P v → Q v s

variable (Q : val → state → Prop)


/- To define the evaluation rule for arrays, it is useful to first define
   the notion of consecutive locations -/

def conseq {B : Type} (vs : List B) (l : Nat) : Finmap (fun _ : Nat ↦ B) :=
  match vs with
  | [] => ∅
  | v :: vs' => (Finmap.singleton l v) ∪ (conseq vs' (l + 1))

lemma conseq_nil B (l : Nat) :
  conseq ([] : List B) l = ∅ := by
  sdone

lemma conseq_cons B (l : Nat) (v : B) (vs : List B) :
  conseq (v :: vs) l = (Finmap.singleton l v) ∪ (conseq vs (l + 1)) := by
  sdone

lemma disjoint_single_conseq B l l' L (v : B) :
  (l < l') ∨ (l ≥ l' + L.length) →
  Finmap.Disjoint (Finmap.singleton l v) (conseq L l') := by
  induction L generalizing l' with
  | nil          =>
      srw conseq_nil Finmap.Disjoint.symm_iff=> ?
      apply Finmap.disjoint_empty
  | cons h t ih =>
      srw conseq_cons Finmap.disjoint_union_right /= => [] ? ⟨|⟩
      { sby move=> ? ; srw Not ?Finmap.mem_singleton }
      { sby apply ih }
      { move=> ? ; srw Not ?Finmap.mem_singleton ; omega }
      { apply ih ; omega }

/- For initializing a list with value v -/
def make_list {A} (n : Nat) (v : A) : List A :=
  match n with
  | 0      => []
  | n' + 1 => v :: make_list n' v

def test1 : Finmap (fun _ : ℕ ↦ ℕ) := Finmap.singleton 0 1
def test2 : Finmap (fun _ : ℕ ↦ ℕ) := Finmap.singleton 1 2

-- #reduce test1 \ test2
-- { entries := Quot.mk List.Perm [⟨0, 1⟩], nodupKeys := ⋯ }


/- Big-step relation -/
inductive eval : state → trm → (val → state → Prop) -> Prop where
  | eval_val : forall s v Q,
      Q v s ->
      eval s (trm_val v) Q
  | eval_fun : forall s x t1 Q,
      Q (val_fun x t1) s ->
      eval s (trm_fun x t1) Q
  | eval_fix : forall s f x t1 Q,
      Q (val_fix f x t1) s ->
      eval s (trm_fix f x t1) Q
  | eval_app_arg1 : forall s1 t1 t2 Q1 Q,
      ¬ trm_is_val t1 ->
      eval s1 t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> eval s2 (trm_app v1 t2) Q) ->
      eval s1 (trm_app t1 t2) Q
  | eval_app_arg2 : forall s1 (v1 : val) t2 Q1 Q,
      ¬ trm_is_val t2 ->
      eval s1 t2 Q1 ->
      (forall v2 s2, Q1 v2 s2 -> eval s2 (trm_app v1 v2) Q) ->
      eval s1 (trm_app v1 t2) Q
  | eval_app_fun : forall s1 v1 (v2 :val) x t1 Q,
      v1 = val_fun x t1 ->
      eval s1 (subst x v2 t1) Q ->
      eval s1 (trm_app v1 v2) Q
  | eval_app_fix : forall s (v1 v2 : val) f x t1 Q,
      v1 = val_fix f x t1 ->
      eval s (subst x v2 (subst f v1 t1)) Q ->
      eval s (trm_app v1 v2) Q
  | eval_seq : forall Q1 s t1 t2 Q,
      eval s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> eval s2 t2 Q) ->
      eval s (trm_seq t1 t2) Q
  | eval_let : forall Q1 s x t1 t2 Q,
      eval s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> eval s2 (subst x v1 t2) Q) ->
      eval s (trm_let x t1 t2) Q
  | eval_if : forall s (b : Bool) t1 t2 Q,
      eval s (if b then t1 else t2) Q ->
      eval s (trm_if (val_bool b) t1 t2) Q
  | eval_unop : forall op s v1 P Q,
      evalunop op v1 P ->
      purepostin s P Q ->
      eval s (trm_app op v1) Q
  | eval_binop : forall op s (v1 v2 : val) P Q,
      evalbinop op v1 v2 P ->
      purepostin s P Q ->
      eval s (trm_app (trm_app op v1) v2) Q
  | eval_ref : forall s x t1 t2 (Q Q₁ : val → state → Prop),
    eval s t1 Q₁ →
    (∀ v1 s1, Q₁ v1 s1 → ∀ p ∉ s1,
     eval (s1.insert p v1) (subst x p t2) fun v s ↦ Q v (s.erase p)) →
    eval s (trm_ref x t1 t2) Q
  | eval_get : forall s p Q,
      p ∈ s ->
      Q (read_state p s) s ->
      eval s (trm_app val_get (val_loc p)) Q
  | eval_set : forall s p v Q,
      v = trm_val v' ->
      p ∈ s ->
      Q val_unit (Finmap.insert p v' s) ->
      eval s (trm_app (trm_app val_set (val_loc p)) v) Q
  | eval_alloc_arg : forall s Q₁ Q,
    ¬ trm_is_val t1 →
    eval s t1 Q₁ →
    (∀ v' s', Q₁ v' s' → eval s' (trm_alloc x v' t2) Q) →
    eval s (trm_alloc x t1 t2) Q
  | eval_alloc : forall (sa : state) (n : ℤ) Q,
    n ≥ 0 →
    (∀ (p : loc) (sb : state),
      sb = conseq (make_list n.natAbs val_uninit) p →
      p ≠ null →
      Finmap.Disjoint sa sb →
      eval (sb ∪ sa) (subst x p t2) fun v s ↦ Q v (s \ sb)) →
    eval sa (trm_alloc x n t2) Q
  -- | eval_alloc : forall (n : Int) (sa : state) Q,
  --     n ≥ 0 →
  --     ( forall (p : loc) (sb : state),
  --         sb = conseq (make_list n.natAbs val_uninit) p →
  --         p ≠ null →
  --         Finmap.Disjoint sa sb →
  --         Q (val_loc p) (sb ∪ sa) ) →
  --     eval sa (trm_app val_alloc n) Q
  | eval_for (n₁ n₂ : Int) (Q : val -> state -> Prop) :
    eval s (if (n₁ < n₂) then
               (trm_seq (subst x n₁ t₁) (trm_for x (val_int (n₁ + 1)) n₂ t₁))
            else val_unit) Q ->
    eval s (trm_for x n₁ n₂ t₁) Q
  | eval_while (t₁ t₂ : trm) (Q : val -> state -> Prop) :
    eval s t₁ Q₁ ->
    (∀ s v, Q₁ v s -> eval s (trm_if v (trm_seq t₂ (trm_while t₁ t₂)) val_unit) Q) ->
    eval s (trm_while t₁ t₂) Q


/- Not sure if the rules eval_ref and eval_set are correct. I had to add the
   condition [v = trm_val v'] to get the definition to type-check. However, this
   assertion says that the term v is a value but really shouldn't this be
   that v big-steps to a value? Not sure what the best way to do this is.
   Perhaps by doing something like the seq rule where there is some
   intermediate condition Q' for first evaluating v and then composing that
   with the memory allocation. -/

/- Rule for values to instantiate postconditions -/

lemma eval_val_minimal s v :
  eval s (trm_val v) (fun v' s' => (v' = v) /\ (s' = s)) :=
  by sby apply eval.eval_val


/- Special rules to avoid unecessary use of [evalbinop] and [evalunop] -/

lemma eval_add  s n1 n2 Q :
  Q (val_int (n1 + n2)) s →
  eval s (trm_app (trm_app val_add (val_int n1)) (val_int n2)) Q :=
by
  move=> ?
  apply eval.eval_binop
  { apply evalbinop.evalbinop_add }
  sdone

lemma eval_addr s r1 r2 Q :
  Q (val_real (r1 + r2)) s →
  eval s (trm_app (trm_app val_add (val_real r1)) (val_real r2)) Q :=
by
  move=> ?
  apply eval.eval_binop
  { apply evalbinop.evalbinop_addr }
  sdone

lemma eval_div s n1 n2 Q :
  n2 ≠ 0 ->
  Q (val_int (n1 / n2)) s ->
  eval s (trm_app (trm_app val_div (val_int n1)) (val_int n2)) Q :=
by
  move=> *
  apply eval.eval_binop
  { apply evalbinop.evalbinop_div=>// }
  sdone

lemma eval_divr s r1 r2 Q :
  r2 ≠ 0 ->
  Q (val_real (r1 / r2)) s ->
  eval s (trm_app (trm_app val_div (val_real r1)) (val_real r2)) Q :=
by
  move=> *
  apply eval.eval_binop
  { apply evalbinop.evalbinop_divr=>// }
  sdone

-- lemma eval_rand s (n : ℤ) Q :
--   n > 0 ->
--   (forall n1, 0 <= n1 ∧ n1 < n -> Q n1 s) ->
--   eval s (trm_app val_rand (val_int n)) Q :=
-- by
--   move=> *
--   apply eval.eval_unop
--   { apply evalunop.evalunop_rand=>// }
--   sby move=> ? []


/- Derived rules for reasoning about applications that don't require checking
   if terms are already values -/

lemma eval_app_arg1' s1 t1 t2 Q1 Q :
  eval s1 t1 Q1 ->
  (forall v1 s2, Q1 v1 s2 -> eval s2 (trm_app v1 t2) Q) ->
  eval s1 (trm_app t1 t2) Q :=
by
  move=> hevals1 hevals2
  scase: [(trm_is_val t1)]=> hVal
  { sby apply eval.eval_app_arg1 }
  sby scase: t1=> // ? []

/- TODO: optimise (similar to ↑) -/
lemma eval_app_arg2' : forall s1 (v1 : val) t2 Q1 Q,
  eval s1 t2 Q1 ->
  (forall v2 s2, eval s2 (trm_app v1 v2) Q) ->
  eval s1 (trm_app v1 t2) Q :=
by
  move=> s1 v1 t2 Q1 Q hevals1 hevals2
  scase: [(trm_is_val t2)]=> hVal
  { apply eval.eval_app_arg2=>// }
  sby scase: t2


/- [eval_like t1 t2] asserts that [t2] evaluates like [t1], i.e.,
    this relation holds whenever [t2] reduces in small-step to [t1]. -/
def eval_like (t1 t2:trm) : Prop :=
  forall s Q, eval s t1 Q -> eval s t2 Q

-- lemma eval_app_arg1_inv s1 t1 t2 Q :
--   eval s1 (trm_app t1 t2) Q ->
--   ¬ trm_is_val t1 ->
--   ∃ Q1, eval s1 t1 Q1 ∧
--     (forall v1 s2, Q1 v1 s2 -> eval s2 (trm_app v1 t2) Q) := by
--     scase=> //==
--     { move=> Q1 *; exists Q1 }


inductive evalExact : state → trm → (val → state → Prop) -> Prop where
  | val : forall s v,
      evalExact s (trm_val v) (fun v' s' ↦ v' = v ∧ s' = s)
  | fun : forall s x t1,
      evalExact s (trm_fun x t1) (fun v' s' ↦ v' = val_fun x t1 ∧ s' = s)
  | fix : forall s f x t1,
      evalExact s (trm_fix f x t1) (fun v' s' ↦ v' = val_fix f x t1 ∧ s' = s)
  | app_arg1 : forall s1 t1 t2 Q1 Q,
      ¬ trm_is_val t1 ->
      evalExact s1 t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> evalExact s2 (trm_app v1 t2) Q) ->
      evalExact s1 (trm_app t1 t2) Q
  | app_arg2 : forall s1 (v1 : val) t2 Q1 Q,
      ¬ trm_is_val t2 ->
      evalExact s1 t2 Q1 ->
      (forall v2 s2, Q1 v2 s2 -> evalExact s2 (trm_app v1 v2) Q) ->
      evalExact s1 (trm_app v1 t2) Q
  | app_fun : forall s1 v1 (v2 :val) x t1 Q,
      v1 = val_fun x t1 ->
      evalExact s1 (subst x v2 t1) Q ->
      evalExact s1 (trm_app v1 v2) Q
  | app_fix : forall s (v1 v2 : val) f x t1 Q,
      v1 = val_fix f x t1 ->
      evalExact s (subst x v2 (subst f v1 t1)) Q ->
      evalExact s (trm_app v1 v2) Q
  | seq : forall Q1 s t1 t2 Q,
      evalExact s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> evalExact s2 t2 Q) ->
      evalExact s (trm_seq t1 t2) Q
  | let : forall Q1 s x t1 t2 Q,
      evalExact s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> evalExact s2 (subst x v1 t2) Q) ->
      evalExact s (trm_let x t1 t2) Q
  | if : forall s (b : Bool) t1 t2 Q,
      evalExact s (if b then t1 else t2) Q ->
      evalExact s (trm_if (val_bool b) t1 t2) Q
  | unop : forall op s v1 P,
      evalunop op v1 P ->
      evalExact s (trm_app op v1) (purepost s P)
  | binop : forall op s (v1 v2 : val) P,
      evalbinop op v1 v2 P ->
      evalExact s (trm_app (trm_app op v1) v2) (purepost s P)
  | ref : forall s x t1 t2 Q Q₁,
    evalExact s t1 Q₁ →
    (∀ v1 s1, Q₁ v1 s1 → ∀ p ∉ s1,
     evalExact (s1.insert p v1) (subst x p t2) fun v s ↦ Q v (s.erase p)) →
      evalExact s (trm_ref x t1 t2) Q
  | get : forall s p,
      p ∈ s ->
      evalExact s (trm_app val_get (val_loc p))
        (fun v' s' ↦ v' = read_state p s ∧ s' = s)
  | set : forall s p v,
      v = trm_val v' ->
      p ∈ s ->
      evalExact s (trm_app (trm_app val_set (val_loc p)) v)
        (fun v'' s' ↦ v'' = val_unit ∧ s' = s.insert p v')
  | alloc_arg : forall s Q₁ Q,
    ¬ trm_is_val t1 →
    evalExact s t1 Q₁ →
    (∀ v' s', Q₁ v' s' → evalExact s' (trm_alloc x v' t2) Q) →
    evalExact s (trm_alloc x t1 t2) Q
  | alloc : forall (sa : state) (n : ℤ) Q,
    n ≥ 0 →
    (∀ (p : loc) (sb : state),
      sb = conseq (make_list n.natAbs val_uninit) p →
      p ≠ null →
      Finmap.Disjoint sa sb →
      evalExact (sb ∪ sa) (subst x p t2) fun v s ↦ Q v (s \ sb)) →
    evalExact sa (trm_alloc x n t2) Q
  -- | alloc : forall (n : Int) (sa : state),
  --     n ≥ 0 →
  --     evalExact sa (trm_app val_alloc n)
  --       (fun v s ↦ ∃ p, p ≠ null ∧ v = p ∧
  --                     sa.Disjoint (conseq (make_list n.natAbs val_uninit) p) ∧
  --                     s = conseq (make_list n.natAbs val_uninit) p ∪ sa )
  | for (n₁ n₂ : Int) (Q : val -> state -> Prop) :
    evalExact s (if (n₁ < n₂) then
               (trm_seq (subst x n₁ t₁) (trm_for x (val_int (n₁ + 1)) n₂ t₁))
            else val_unit) Q ->
    evalExact s (trm_for x n₁ n₂ t₁) Q
  | while (t₁ t₂ : trm) (Q Q₁ : val -> state -> Prop) :
    evalExact s t₁ Q₁ ->
    (∀ s v, Q₁ v s -> evalExact s (trm_if v (trm_seq t₂ (trm_while t₁ t₂)) val_unit) Q) ->
    evalExact s (trm_while t₁ t₂) Q


def evalExact_ref_nonpositive s x t1 t2 (Q : val → state → Prop) :=
  ∃ Q₁, evalExact s t1 Q₁ ∧
  (∀ v1 s1, Q₁ v1 s1 → ∀ p ∉ s1,
    (evalExact (s1.insert p v1) (subst x p t2) (fun v s ↦ Q v (s.erase p))))

def val.is_loc : val -> Prop
  | val_loc _ => True
  | _ => False

-- example :
--   evalExact_ref_nonpositive ∅ "x" (trm_val (val_int 0)) (trm_var "x") fun v h => v.is_loc ∧ h = ∅ := by
--   unfold evalExact_ref_nonpositive
--   exists (fun v s ↦ v = 0 ∧ s = ∅)=> ⟨//| ⟩
--   move=> > /= [->->] > ? ; simp [subst]
--   admit

lemma evalExact_post_eq :
  Q = Q' →
  evalExact s t Q →
  evalExact s t Q' := by sdone

lemma exact_imp_eval :
  evalExact s t Q → eval s t Q := by
  elim=> >
  { sby constructor }
  { sby constructor }
  { sby constructor }
  { move=> * ; sby constructor }
  { move=> * ; sby apply eval.eval_app_arg2 }
  { move=> * ; sby apply eval.eval_app_fun }
  { move=> * ; sby apply eval.eval_app_fix }
  { move=> ??? h ; apply (eval.eval_seq Q1)=>// ; exact h }
  { move=> * ; sby constructor }
  { move=> * ; sby constructor }
  { move=> * ; apply eval.eval_unop=> //
    sby unfold purepostin purepost }
  { move=> * ; apply eval.eval_binop=> //
    sby unfold purepostin purepost }
  { move=> * ; sby apply eval.eval_ref }
  { move=> * ; sby apply eval.eval_get }
  { move=> * ; sby apply eval.eval_set }
  { move=> * ; sby apply eval.eval_alloc_arg }
  { move=> * ; sby apply eval.eval_alloc }
  { move=> ?ih ; sby constructor }
  move=> * ; sby constructor


end eval


/- ================================================================= -/
/-* ** Notation for Concrete Terms -/

def trm_apps (f:trm) (ts:List trm) : trm :=
  match ts with
  | [] => f
  | ti::ts' => trm_apps (trm_app f ti) ts'

def trm_funs (xs:List var) (t:trm) : trm :=
  match xs with
  | [] => t
  | x1::xs' => trm_fun x1 (trm_funs xs' t)

def val_funs (xs:List var) (t:trm) : val :=
  match xs with
  | [] => panic! "function with zero argumets!"
  | x1::xs' => val_fun x1 (trm_funs xs' t)

def trm_fixs (f:var) (xs:List var) (t:trm) : trm :=
  match xs with
  | [] => t
  | x1::xs' => trm_fix f x1 (trm_funs xs' t)

def val_fixs (f:var) (xs:List var) (t:trm) : val :=
  match xs with
  | .nil => val_uninit
  | x1::xs' => val_fix f x1 (trm_funs xs' t)

end

open trm val prim

declare_syntax_cat lang
declare_syntax_cat bop
declare_syntax_cat uop

-- #check let x := (); let y := (); y
-- x; y
/-
  x;
  y
-/

syntax ident : lang
syntax num : lang
syntax:20 lang "; " (ppDedent(ppLine lang)) : lang
syntax:25 lang ppSpace lang:30 : lang
syntax "if " lang "then " lang "end " : lang
syntax ppIndent("if " lang " then") ppSpace lang ppDedent(ppSpace) ppRealFill("else " lang) : lang
syntax "let" ident " := " lang " in" ppDedent(ppLine lang) : lang
syntax "ref" ident " := " lang " in" ppDedent(ppLine lang) : lang
syntax "alloc" lang " as " ident " in" ppDedent(ppLine lang) : lang
syntax "for" ident " in " "[" lang " : " lang "]" " {"  (ppLine lang) ( " }") : lang
syntax "while" lang  " {"  (ppLine lang) ( " }") : lang
-- TODO: I suspect it should be  `withPosition(lang ";") ppDedent(ppLine lang) : lang`, but Lean parser crashes. Report a bug.
syntax "fun" ident+ " => " lang : lang
syntax "fix" ident ident+ " => " lang : lang
syntax "fun_ " ident* " => " lang : lang
syntax "fix_ " ident ident* " => " lang : lang
syntax "()" : lang
syntax uop lang:30 : lang
syntax lang:30 bop lang:30 : lang
syntax "(" lang ")" : lang
syntax "⟨" term "⟩" : lang
syntax "⟨" term ":" term "⟩" : lang

syntax " := " : bop
syntax " + " : bop
syntax " - " : bop
syntax " * " : bop
syntax " / " : bop
syntax " < " : bop
syntax " > " : bop
syntax " <= " : bop
syntax " >= " : bop
syntax " = " : bop
syntax " != " : bop
syntax " mod " : bop
syntax " ++ " : bop

syntax "!" : uop
syntax "-" : uop
-- syntax "ref" : uop
syntax "free" : uop
syntax "not" : uop
syntax "mkarr" : uop

syntax "len" : uop
syntax lang noWs "[" lang "]" : lang
-- syntax lang noWs "[" lang "] := " lang : lang
-- syntax "mkarr" lang ", " lang : lang
-- t:term --> [lang| l : lang]
-- trm_seq t₁ t₂

syntax "[lang| " lang "]" : term
syntax "[bop| " bop "]" : term
syntax "[uop| " uop "]" : term


local notation "%" x => (Lean.quote (toString (Lean.Syntax.getId x)))

macro_rules
  | `([lang| ()])                       => `(trm_val (val_unit))
  | `([lang| $n:num])                   => `(trm_val (val_int $n))
  | `([lang| $t1 $t2])                  => `(trm_app [lang| $t1] [lang| $t2])
  | `([lang| if $t1 then $t2 else $t3]) => `(trm_if [lang| $t1] [lang| $t2] [lang| $t3])
  | `([lang| if $t1 then $t2 end])      => `(trm_if [lang| $t1] [lang| $t2] (trm_val val_unit))
  | `([lang| let $x := $t1:lang in $t2:lang])     =>
    `(trm_let $(%x) [lang| $t1] [lang| $t2])
  | `([lang| ref $x := $t1:lang in $t2:lang])     =>
    `(trm_ref $(%x) [lang| $t1] [lang| $t2])
  | `([lang| alloc $t1:lang as $x in $t2:lang])   =>
    `(trm_alloc $(%x) [lang| $t1] [lang| $t2])
  | `([lang| $t1 ; $t2])                => `(trm_seq [lang| $t1] [lang| $t2])
  | `([lang| fun_ $xs* => $t])             => do
    let xs <- xs.mapM fun x => `(term| $(%x))
    `(trm_funs [ $xs,* ] [lang| $t])
  | `([lang| fun $xs* => $t])             => do
    let xs <- xs.mapM fun x => `(term| $(%x))
    `(val_funs [ $xs,* ] [lang| $t])
  | `([lang| fix_ $f $xs* => $t])    => do
      let xs <- xs.mapM fun x => `(term| $(%x))
      `(trm_fixs $(%f) [ $xs,* ] [lang| $t])
  | `([lang| fix $f $xs* => $t])    => do
      let xs <- xs.mapM fun x => `(term| $(%x))
      `(val_fixs $(%f) [ $xs,* ] [lang| $t])
  -- | `([lang| ref $t])                   => `(trm_val (val_prim val_ref) [lang| $t])
  | `([lang| free $t])                  => `(trm_val (val_prim val_free) [lang| $t])
  | `([lang| not $t])                   => `(trm_val (val_prim val_not) [lang| $t])
  -- | `([lang| alloc $n])                => `(trm_val (val_alloc) [lang| $n])
  | `([lang| !$t])                      => `(trm_val val_get [lang| $t])
  | `([lang| $t1 := $t2])               => `(trm_val val_set [lang| $t1] [lang| $t2])
  | `([lang| $t1 + $t2])                => `(trm_val val_add [lang| $t1] [lang| $t2])
  | `([lang| $t1 * $t2])                => `(trm_val val_mul [lang| $t1] [lang| $t2])
  | `([lang| $t1 - $t2])                => `(trm_val val_sub [lang| $t1] [lang| $t2])
  | `([lang| $t1 / $t2])                => `(trm_val val_div [lang| $t1] [lang| $t2])
  | `([lang| $t1 < $t2])                => `(trm_val val_lt [lang| $t1] [lang| $t2])
  | `([lang| $t1 > $t2])                => `(trm_val val_gt [lang| $t1] [lang| $t2])
  | `([lang| $t1 <= $t2])               => `(trm_val val_le [lang| $t1] [lang| $t2])
  | `([lang| $t1 >= $t2])               => `(trm_val val_ge [lang| $t1] [lang| $t2])
  | `([lang| -$t])                      => `(trm_val val_opp [lang| $t])
  | `([lang| $t1 = $t2])                => `(trm_val val_eq [lang| $t1] [lang| $t2])
  | `([lang| $t1 != $t2])               => `(trm_val val_neq [lang| $t1] [lang| $t2])
  | `([lang| $t1 mod $t2])              => `(trm_val val_mod [lang| $t1] [lang| $t2])
  | `([lang| $t1 ++ $t2])               => `(trm_val val_ptr_add [lang| $t1] [lang| $t2])
  | `([lang| ($t)]) => `([lang| $t])
  | `([lang| ⟨$t : $tp⟩]) => `(trm_val (($t : $tp)))
  | `([lang| for $x in [$n1 : $n2] { $t } ]) =>
    `(trm_for $(%x) [lang| $n1] [lang| $n2] [lang| $t])
  | `([lang| while $c:lang { $t:lang } ]) =>
     `(trm_while [lang| $c] [lang| $t] )

open Lean Elab Term
elab_rules : term
  | `([lang| $x:ident]) => do
    try do
      (<- withoutErrToSorry <| elabTermAndSynthesize x none).ensureHasNoMVars
      elabTerm (<- `(trm_val $x)) none
    catch _ => do
      let x <- `(trm_var $(%x))
      elabTerm x none

elab_rules : term
  | `([lang| ⟨$t⟩]) => do
    let te <- elabTerm t none
    let tp <- Meta.inferType te
    let tp <- delabPpAll tp
    elabTerm (<- `(trm_val ($t : $tp))) none


def val_abs : val := [lang|
  fun i =>
    let c := i < 0 in
    let m := 0 - 1 in
    let j := m * i in
    if c then j else i ]

def val_array_get : val := [lang|
  fun p i =>
    let p1 := p ++ 1 in
    let q := p1 ++ i in
    !q ]

def val_array_set : val := [lang|
  fun p i v =>
    let p1 := p ++ 1 in
    let q := p1 ++ i in
    q := v ]

def val_array_length : val := [lang|
  fun p => !p ]

def default_get d := [lang|
  fun p i =>
    let n := val_abs i in
    let l := val_array_length p in
    let b := n < l in
    if b then
      val_array_get p n
    else
      d ]

def default_set : val := [lang|
  fun p i v =>
      let i := val_abs i in
      let L := val_array_length p in
      let b := i < L in
      if b then
        val_array_set p i v
      else
        () ]

def val_array_fill : val := [lang|
  fix f p i n v =>
    let b := n > 0 in
    if b then
      ((val_array_set p) i) v ;
      let m := n - 1 in
      let j := i + 1 in
      f p j m v
    end ]

def val_array_make : val := [lang|
  fun n v =>
    let m := n + 1 in
    alloc m as p in
    (val_set p) n ;
    (((val_array_fill p) 0) n) v ;
    p ]

abbrev default_get' := default_get (val_int 0)

macro_rules
  | `([lang| len $p])                => `(trm_val val_array_length [lang| $p])
  | `([lang| $arr[$i] ])              => `(trm_val val_array_get [lang| $arr] [lang| $i])
  -- | `([lang| $arr[$i]($d)])           => `(trm_val default_get [lang| $arr] [lang| $i] [lang| $d])
  | `([lang| $arr[$i] := $v])        => `(trm_app val_array_set [lang| $arr] [lang| $i] [lang| $v])
  | `([lang| mkarr $n:lang $v:lang]) => `(trm_val val_array_make [lang| $n] [lang| $v])


@[app_unexpander val_unit] def unexpandUnitL : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `([lang| ()])
  -- | _ => throw ( )

@[app_unexpander val_int] def unexpandInt : Lean.PrettyPrinter.Unexpander
  | `($(_) $n:num) => `($n:num)
  | `($(_) $n:ident) => `($n:ident)
  | `($(_) $n:term) => `(lang|⟨$n:term⟩)
  | _ => throw ( )

@[app_unexpander val_real] def unexpandReal : Lean.PrettyPrinter.Unexpander
  | `($(_) $n:num) => `($n:num)
  | `($(_) $n:ident) => `($n:ident)
  | `($(_) $n:term) => `(lang|⟨$n:term⟩)
  | _ => throw ( )

@[app_unexpander val_loc] def unexpandLoc : Lean.PrettyPrinter.Unexpander
  | `($(_) $n:ident) => `($n:ident)
  | `($(_) $n:term) => `(lang|⟨$n:term⟩)
  | _ => throw ( )

@[app_unexpander val_bool] def unexpandBool : Lean.PrettyPrinter.Unexpander
  | `($(_) $n:ident) => `($n:ident)
  | `($(_) $n:term) => `(lang|⟨$n:term⟩)
  | _ => throw ( )

@[app_unexpander val_prim] def unexpandPrim : Lean.PrettyPrinter.Unexpander
  -- | `($(_) val_ref) => `([uop| ref])
  | `($(_) val_free) => `([uop| free])
  | `($(_) val_not) => `([uop| not])
  | `($(_) val_opp) => `([uop| -])
  | `($(_) val_get) => `([uop| !])
  | `($(_) val_add) => `([bop| +])
  | `($(_) val_mul) => `([bop| *])
  | `($(_) val_sub) => `([bop| -])
  | `($(_) val_div) => `([bop| /])
  | `($(_) val_lt) => `([bop| <])
  | `($(_) val_gt) => `([bop| >])
  | `($(_) val_le) => `([bop| <=])
  | `($(_) val_ge) => `([bop| >=])
  | `($(_) val_eq) => `([bop| =])
  | `($(_) val_neq) => `([bop| !=])
  | `($(_) val_mod) => `([bop| mod])
  | `($(_) val_set) => `([bop| :=])
  | `($(_) val_ptr_add) => `([bop| ++])
  | _ => throw ( )

@[app_unexpander trm_val] def unexpandVal : Lean.PrettyPrinter.Unexpander := fun x =>
  match x with
  | `($(_) $x:ident) =>
    match x with
    | `(val_array_get) => `($x)
    | `(val_array_set) => `($x)
    | `(val_unit) => `([lang| ()])
    | `(val_array_make) => `([uop| mkarr])
    | _ => `([lang| $x:ident])
  | `($(_) $x) =>
    match x with
    | `($n:num) => `([lang| $n:num])
    | `($n:ident) => `([lang| $n:ident])
    | `(lang|⟨$n:term⟩) => `([lang| ⟨$n⟩])
    | `([lang| $_]) => return x
    | `([uop| $_]) => return x
    | `([bop| $_]) => return x
    | t => `([lang| ⟨$t⟩])
  | _ => throw ( )
instance : Coe ℝ val := ⟨val_real⟩
-- #check fun (i : ℤ -> ℤ) => [lang| ⟨i 0 : ℤ⟩]

@[app_unexpander trm_app] def unexpandApp : Lean.PrettyPrinter.Unexpander := fun x => do
  -- dbg_trace x
  match x with
  | `($(_) [uop|$uop] [lang| $t]) => `([lang| $uop:uop$t])
  | `($(_) $app [lang| $t2]) =>
    -- dbg_trace app
    match app with
    | `([bop| $bop].trm_app [lang| $t1]) => `([lang| $t1 $bop $t2])
    | `([lang| $t1]) => `([lang| $t1 $t2])
    | `(val_array_get) => return x
    | `(trm_app val_array_get [lang| $t1]) => `([lang| $t1[$t2] ])
    | `(val_array_set) => return x
    | `(trm_app val_array_set [lang| $_]) => return x
    | `(trm_app $app [lang| $t1]) =>
      match app with
      | `(trm_app val_array_set [lang| $t0]) => `([lang| $t0[$t1] := $t2])
      -- | `(trm_app default_get [lang| $t0]) =>
      --   -- dbg_trace t2
      --   match t2 with
      --   | `(lang| ()) => `([lang| $t0[$t1]])
      --   | _ => `([lang| $t0[$t1]($t2)])
      | _ => throw ( )
    | _ => throw ( )
  | `($(_) [bop| $bop] [lang| $t1]) => return x
  -- | `($(_) [lang| $t] [lang| $t1]) =>
  --   match t with
  --   | `(lang| default_get $t2) => `([lang| $t2[$t1]])
  --   | _ => throw ( )
  | _ => throw ( )

@[app_unexpander trm_var] def unexpandVar : Lean.PrettyPrinter.Unexpander
  | `($(_) $x:str) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| $name:ident])
  | _ => throw ( )

@[app_unexpander trm_seq] def unexpandSeq : Lean.PrettyPrinter.Unexpander
  | `($(_) [lang| $t1] [lang| $t2]) => `([lang| $t1 ; $t2])
  | _ => throw ( )

@[app_unexpander trm_let] def unexpandLet : Lean.PrettyPrinter.Unexpander
  | `($(_) $x:str [lang| $t1] [lang| $t2]) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| let $name := $t1 in $t2])
  | _ => throw ( )

@[app_unexpander trm_ref] def unexpandRef : Lean.PrettyPrinter.Unexpander
  | `($(_) $x:str [lang| $t1] [lang| $t2]) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| ref $name := $t1 in $t2])
  | _ => throw ( )

@[app_unexpander trm_alloc] def unexpandAlloc : Lean.PrettyPrinter.Unexpander
  | `($(_) $x:str [lang| $t1] [lang| $t2]) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| alloc $t1 as $name in $t2])
  | _ => throw ( )

@[app_unexpander trm_for] def unexpandFor : Lean.PrettyPrinter.Unexpander
  | `($(_) $x:str [lang| $n1] [lang| $n2] [lang| $t]) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| for $name in [$n1 : $n2] { $t } ])
  | _ => throw ( )

@[app_unexpander trm_while] def unexpandWhile : Lean.PrettyPrinter.Unexpander
  | `($(_) [lang| $c] [lang| $t]) => do
    `([lang| while $c { $t:lang } ])
  | _ => throw ( )

@[app_unexpander trm_if] def unexpandIf : Lean.PrettyPrinter.Unexpander
  | `($(_) [lang| $t1] [lang| $t2] [lang| $t3]) => `([lang| if $t1 then $t2 else $t3])
  | _ => throw ( )

@[app_unexpander trm_fun] def unexpandTFun : Lean.PrettyPrinter.Unexpander
  | `($(_) $x:str [lang| fun $xs* => $t]) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| fun $name $xs* => $t])
  | `($(_) $x:str [lang| $t]) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| fun $name => $t])
  | _ => throw ( )

/-
  trm_for "x" n1 n2 t
-/

@[app_unexpander val_fun] def unexpandVFun : Lean.PrettyPrinter.Unexpander
  | `($(_) $x:str [lang| fun $xs* => $t]) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| fun $name $xs* => $t])
  | `($(_) $x:str [lang| $t]) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| fun $name => $t])
  | _ => throw ( )

@[app_unexpander trm_fix] def unexpandTFix : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:str $x:str [lang| fun $xs* => $t]) =>
    let f := f.getString
    let x := x.getString
    let nameF := Lean.mkIdent $ Lean.Name.mkSimple f
    let nameX := Lean.mkIdent $ Lean.Name.mkSimple x
    `([lang| fix $nameF $nameX $xs* => $t])
  | `($(_) $f:str $x:str [lang| $t]) =>
    let f := f.getString
    let x := x.getString
    let nameF := Lean.mkIdent $ Lean.Name.mkSimple f
    let nameX := Lean.mkIdent $ Lean.Name.mkSimple x
    `([lang| fix $nameF $nameX => $t])
  | _ => throw ( )

@[app_unexpander val_fix] def unexpandVFix : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:str $x:str [lang| fun $xs* => $t]) =>
    let f := f.getString
    let x := x.getString
    let nameF := Lean.mkIdent $ Lean.Name.mkSimple f
    let nameX := Lean.mkIdent $ Lean.Name.mkSimple x
    `([lang| fix $nameF $nameX $xs* => $t])
  | `($(_) $f:str $x:str [lang| $t]) =>
    let f := f.getString
    let x := x.getString
    let nameF := Lean.mkIdent $ Lean.Name.mkSimple f
    let nameX := Lean.mkIdent $ Lean.Name.mkSimple x
    `([lang| fix $nameF $nameX => $t])
  | _ => throw ( )

-- @[app_unexpander val_alloc] def unexpandVAlloc : Lean.PrettyPrinter.Unexpander
--   | `($(_) [lang| $n]) => `([lang| alloc $n])
--   | _ => throw ( )

-- @[app_unexpander trm_apps] def unexpandApps : Lean.PrettyPrinter.Unexpander
--   -- Unexpand function applications when arguments are program-variables
--   | `($(_) [lang| $f] [ $[[lang|$xs]],* ]) => `([lang| $f  $xs )])
--   -- | `($(_) $f:ident [ $[[lang|$xs]],* ]) => `([lang| $f:ident ( $xs,* )])
--   -- Unexpand function applications when arguments are meta-variables
--   | `($(_) $f:ident [ $xs:term,* ]) => do
--     -- hack to workaround the fact that elements of `xs` are identifiers with
--     -- explicit coercions: [val_loc p, val_int n, ....]
--     let x <- xs.getElems.mapM fun
--        | `($(_) $i:ident) => `(ident| $i:ident)
--        | _ => throw ( )
--     `([lang| $f:ident ( $[ $x:ident],* )])
--   | _ => throw ( )

@[app_unexpander trm_funs] def unexpandTFuns : Lean.PrettyPrinter.Unexpander
  | `($(_) [ $xs:str,* ] [lang| $f]) =>
    let xs := xs.getElems.map (Lean.mkIdent $ Lean.Name.mkSimple ·.getString)
    `([lang| fun $xs* => $f])
  | _ => throw ( )

@[app_unexpander val_funs] def unexpandVFuns : Lean.PrettyPrinter.Unexpander := fun x =>
  match x with
  | `($(_) [ $xs:str,* ] [lang| $f]) =>
    let xs := xs.getElems.map (Lean.mkIdent $ Lean.Name.mkSimple ·.getString)
    `([lang| fun $xs* => $f])
  | _ => throw ( )

@[app_unexpander trm_fixs] def unexpandTFixs : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:str [ $xs:str,* ] [lang| $t]) =>
    let xs := xs.getElems.map (Lean.mkIdent $ Lean.Name.mkSimple ·.getString)
    let f := Lean.mkIdent $ Lean.Name.mkSimple f.getString
    `([lang| fix $f $xs* => $t])
  | _ => throw ( )

@[app_unexpander val_fixs] def unexpandVFixs : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:str [ $xs:str,* ] [lang| $t]) =>
    let xs := xs.getElems.map (Lean.mkIdent $ Lean.Name.mkSimple ·.getString)
    let f := Lean.mkIdent $ Lean.Name.mkSimple f.getString
    `([lang| fix $f $xs* => $t])
  | _ => throw ( )

-- set_option pp.notation false
-- #check [lang| x[3] ]
-- #check [lang| x[7](0)]
-- #check [lang| x[3] := 5; mkarr 5 5]

-- #check fun (p : loc)  => [lang|
--   fix f y z =>
--     if F y z
--     then
--       let y := ⟨1 + 1⟩in
--       let y := 1 + 1 in
--       let y := ⟨0 + 1⟩ in
--       let z := !p in
--       y + z
--     else
--       let y := 1 + 1 in
--       let z := 1 in
--       y + z]

-- #check [lang| x; let x := !x in let y:= () in x]
-- #check [lang|x y; z]
-- #check [lang|!x; y]
-- instance : HAdd ℤ ℕ val := ⟨fun x y => val_int (x + (y : Int))⟩
-- #check fun n : ℤ => (([lang| ()]).trm_seq (trm_val ((n + 1))))

-- #check fun (p : loc)  => [lang|
--   fix f y z =>
--     if F y z
--     then
--       for i in [z : y] {
--         ref z := i in
--         ref x := i in
--         !z
--       }
--     else
--       for i in [z : y] {
--         ref z := i in
--         ref x := i in
--         i := ⟨true⟩;
--         i := i +1;
--         !z
--       }; !z]


-- -- #print val_array_make

-- -- -- set_option pp.notation false
-- -- #check fun (p : loc)  => [lang|
-- --   fix f y z =>
-- --     if F y z
-- --     then
-- --       let y := ⟨1 + 1 : ℝ⟩in
-- --       let y := 1 + 1 in
-- --       let z := !p in
-- --       y + z
-- --     else
-- --       let y := 1 + 1 in
-- --       let z := 1 in
-- --       while (i < z) {
-- --         i := i + 1;
-- --         i := i + 1;
-- --         i}
-- --       ]
-- -- #check [lang| 1 ++ 2]
-- -- #check [lang| let x := 6 in alloc(x) as y in ()]

-- -- #check fun (x : ℤ -> ℝ) => [lang| ⟨x 0 : ℝ⟩]

-- -- #check fun (p : loc)  => [lang|
-- --   fix f y z =>
-- --     if F y z
-- --     then
-- --       let y := ⟨1 + 1⟩in
-- --       let y := 1 + 1 in
-- --       let z := !p in
-- --       y + z
-- --     else
-- --       let y := 1 + 1 in
-- --       let z := 1 in
-- --       while (i < z) {
-- --         i := i + 1;
-- --         i := i + 1;
-- --         i}
-- --       ]
