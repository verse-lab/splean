-- import Ssreflect.Lang
import Mathlib.Data.Finmap

import Lgtm.Unary.Lang
import Lgtm.Unary.Util


open Classical


/- ====================== Heap Predicates ====================== -/

-- namespace hprop_scope
-- open hprop_scope

/- The type of heap predicates is named [hProp]. -/

abbrev hProp := heap -> Prop

/- Entailment for heap predicates, written [H1 ==> H2]. This entailment
    is linear. -/

abbrev himpl (H1 H2 : hProp) : Prop :=
  forall h, H1 h -> H2 h

infixr:51 " ==> " => himpl

/- Entailment between postconditions, written [Q1 ===> Q2]. -/

def qimpl {A} (Q1 Q2 : A → hProp) : Prop :=
  forall (v:A), Q1 v ==> Q2 v

infixr:51 " ===> " => qimpl

/- --------- Definitions of Heap predicates --------- -/

def hempty : hProp :=
  fun h => (h = ∅)

def hsingle (p : loc) (v : val) : hProp :=
  fun h => (h = Finmap.singleton p v)

def hstar (H1 H2 : hProp) : hProp :=
  fun h => exists h1 h2,
    H1 h1 ∧ H2 h2 ∧ Finmap.Disjoint h1 h2 ∧ h = h1 ∪ h2

def hexists {A} (J : A → hProp) : hProp :=
  fun h => exists x, J x h

def hforall {A} (J : A → hProp) : hProp :=
  fun h => forall x, J x h

notation:max "emp" => hempty
-- notation:max "" => hempty

infixr:60 " ~~> " => hsingle


-- #check HMul

class HStar (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a * b` computes the product of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hStar : α → β → γ

infixr:55 " ∗ " => HStar.hStar

macro_rules | `($x ∗ $y)   => `(binop% HStar.hStar $x $y)

@[default_instance]
instance : HStar hProp hProp hProp where
  hStar := hstar

/- This notation sucks (`h` prefix is not uniform across other notations)
   But I dunno know what would be a better one -/
section
open Lean.TSyntax.Compat
macro "h∃" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``hexists xs b
macro "h∀" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``hforall xs b
end

@[app_unexpander hexists] def unexpandHExists : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => h∃ $xs:binderIdent*, $b) => `(h∃ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(h∃ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(h∃ ($x:ident : $t), $b)
  | t                                              => pure t

@[app_unexpander hforall] def unexpandHForall : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => h∀ $xs:binderIdent*, $b) => `(h∀ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(h∀ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(h∀ ($x:ident : $t), $b)
  | t                                              => pure t


-- notation3 "exists' " (...) ", " J r:(scoped J => hexists J) => r

/- not quite sure about these two notations:



 notation3 "forall' " (...) ", " J r:(scoped J => hexists J) => r -/

/- TODO: Translate notations for hexists and hforall:

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.-/


/- Derived operators -/

def hpure (P : Prop) : hProp :=
  hexists (fun (_ : P) => emp)

def htop : hProp :=
  hexists (fun (H : hProp) => H)

def hwand (H1 H2 : hProp) : hProp :=
  hexists (fun (H0 : hProp) => H0 ∗ hpure ((H1 ∗ H0) ==> H2))

def qwand {A} (Q1 Q2 : A → hProp) : hProp :=
  hforall (fun (x : A) => hwand (Q1 x) (Q2 x))

/- this a better notation as for me -/
notation:max "⌜" P "⌝" => hpure P

/- ⊤⊤ is very annoynig, let's just overwrite lean's ⊤ -/
notation (priority := high) "⊤" => htop

def qstar {A} (Q : A → hProp) (H : hProp) : A → hProp :=
  fun x => hstar (Q x) H

instance (A : Type) : HStar (A → hProp) hProp (A → hProp) where
  hStar := qstar

-- infixr:54 " ∗ " => qstar

class HWand (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a -∗ b` is the separating implication between `a` and `b`. -/
  hWand : α → β → γ

infixr:55 " -∗ " => HWand.hWand

@[default_instance]
instance : HWand hProp hProp hProp where
  hWand := hwand

instance (α : Type) : HWand (α → hProp) (α → hProp) hProp where
  hWand := qwand

/- ============ Properties of Separation Logic Operators ============ -/

/- ------------ Properties of [himpl] and [qimpl] ------------ -/

lemma himpl_refl H : H ==> H :=
by sdone

lemma himpl_trans H2 H1 H3 :
  (H1 ==> H2) → (H2 ==> H3) → (H1 ==> H3) :=
by
  sby move=> h1h2 ?? /h1h2


lemma himpl_trans_r H2 H1 H3:
  H2 ==> H3 → H1 ==> H2 → H1 ==> H3 :=
by
  move=> /[swap]
  apply himpl_trans

lemma himpl_antisym H1 H2:
  (H1 ==> H2) → (H2 ==> H1) → (H1 = H2) :=
by
  move=> h1imp2 h2imp1
  apply funext ; move=> ? ; apply propext
  apply Iff.intro
  { sby srw (himpl) at h1imp2 }
  { sby srw (himpl) at h2imp1 }

lemma hprop_op_comm (op : hProp → hProp → hProp) :
  (forall H1 H2, op H1 H2 ==> op H2 H1) →
  (forall H1 H2, op H1 H2 = op H2 H1) :=
by
  move=> *
  apply himpl_antisym <;> aesop


/- ---------------- Properties of [hempty] ---------------- -/

lemma hempty_intro : emp ∅ :=
  by srw hempty

lemma hempty_inv h :
  emp h → h = ∅ :=
by sapply

/- ---------------- Properties of [hstar] ---------------- -/

lemma hstar_intro (H1 H2 : hProp) h1 h2 :
  H1 h1 →
  H2 h2 →
  Finmap.Disjoint h1 h2 →
  (H1 ∗ H2) (h1 ∪ h2) :=
by
  sby move=> *

lemma hstar_inv (H1 H2 : hProp) h:
  (H1 ∗ H2) h →
  exists h1 h2, H1 h1 ∧ H2 h2 ∧ Finmap.Disjoint h1 h2 ∧ h = h1 ∪ h2 :=
by
   sapply

lemma hstar_comm H1 H2 :
  H1 ∗ H2 = H2 ∗ H1 :=
by
  apply hprop_op_comm
  move=> > ? /hstar_inv ![>??]
  move=> /[dup] /Finmap.Disjoint.symm ??
  sby srw Finmap.union_comm_of_disjoint

lemma hstar_assoc H1 H2 H3 :
  (H1 ∗ H2) ∗ H3 = H1 ∗ (H2 ∗ H3) :=
by
  apply himpl_antisym=> h
  { scase! => h12 h3 ![h1 h2] ?? ? -> ?
    move=> /Finmap.disjoint_union_left[??] ->
    exists h1, h2 ∪ h3
    sdo 3 apply And.intro=> //
    { sby srw Finmap.disjoint_union_right }
    sby srw Finmap.union_assoc }
  { move=> ![h1 ?? [h2 [h3 ![??? h23eq]]] /h23eq
      /(Finmap.disjoint_union_right h1 h2 h3) [??] /h23eq hU]
    exists (h1 ∪ h2), h3
    sdo 3 apply And.intro=>//
    apply (Iff.mpr (Finmap.disjoint_union_left h1 h2 h3))=> //
    srw (hU) ; apply Eq.symm ; apply Finmap.union_assoc }

lemma hstar_hempty_l H :
  emp ∗ H = H :=
by
  apply himpl_antisym
  { sby move=> ? ![?? /hempty_inv]}
  move=> h ?
  exists ∅, h
  repeat' (constructor=>//)
  apply (Finmap.disjoint_empty h)

lemma hstar_hempty_r H :
  H ∗ emp = H :=
by
  srw (hstar_comm)
  apply hstar_hempty_l

lemma hstar_hexists A (J : A → hProp) H :
  (hexists J) ∗ H = hexists (fun x => (J x) ∗ H) :=
by
  apply himpl_antisym
  { sby move=> ? ![?? []] }
  sby move=> ? [? ![]]

lemma hstar_hforall A (J : A → hProp) H :
  (hforall J) ∗ H ==> hforall (J ∗ H) :=
by
  move=> ? [h1 ![h2 /hforall] * ?]
  sby exists h1, h2

lemma himpl_frame_l H1 H1' H2 :
  H1 ==> H1' →
  (H1 ∗ H2) ==> (H1' ∗ H2) :=
by
  srw himpl=> ?? ![ h1 h2 *]
  sby exists h1, h2

lemma himpl_frame_r H1 H2 H2' :
  H2 ==> H2' →
  (H1 ∗ H2) ==> (H1 ∗ H2') :=
by
  srw himpl=> ?? ![h1 h2 *]
  sby exists h1, h2

lemma himpl_frame_lr H1 H1' H2 H2' :
  H1 ==> H1' →
  H2 ==> H2' →
  (H1 ∗ H2) ==> (H1' ∗ H2') :=
by
  srw !himpl => ??? ![h1 h2 *]
  sby exists h1, h2

lemma himpl_hstar_trans_l H1 H2 H3 H4 :
  H1 ==> H2 →
  H2 ∗ H3 ==> H4 →
  H1 ∗ H3 ==> H4 :=
by
  srw !himpl => ? hStar23 ? ![h1 h3 *]
  apply hStar23
  sby exists h1, h3

lemma himpl_hstar_trans_r H1 H2 H3 H4 :
  H1 ==> H2 →
  H3 ∗ H2 ==> H4 →
  H3 ∗ H1 ==> H4 :=
by
  srw !himpl => ? hStar32 ? ![h3 h1 *]
  apply hStar32
  sby exists h3, h1


/- --------------- Properties of [hpure] --------------- -/

lemma hpure_intro P :
  P → ⌜P⌝  ∅ :=
by sdone

lemma hpure_inv P h :
  ⌜P⌝ h →
  P ∧ h = ∅ :=
by
  sby move=> []

lemma hstar_hpure_l P H h :
  (⌜P⌝ ∗ H) h = (P ∧ H h) :=
by
  srw hpure hstar_hexists hstar_hempty_l
  sby move=> ! ⟨|⟩ []

lemma hstar_hpure_r P H h :
  (H ∗ ⌜P⌝) h = (H h ∧ P) :=
by
  sby srw hstar_comm hstar_hpure_l

lemma himpl_hstar_hpure_r P H H' :
   P →
   (H ==> H') →
   H ==> ⌜P⌝ ∗ H' :=
by
  srw !himpl => *
  sby srw hstar_hpure_l

lemma hpure_inv_hempty P h :
  ⌜P⌝ h →
  P ∧ emp h :=
by
  sby srw -hstar_hpure_l hstar_hempty_r

lemma hpure_intro_hempty P h :
  emp h → P → ⌜P⌝ h :=
by
  sby move=> *

lemma himpl_hempty_hpure P :
  P → emp ==> ⌜P⌝ :=
by
  sby move=> ???

lemma himpl_hstar_hpure_l P H H' :
  (P → H ==> H') →
  (⌜P⌝ ∗ H) ==> H' :=
by
  srw himpl=> * ?
  sby srw hstar_hpure_l

lemma hempty_eq_hpure_true :
  emp = ⌜True⌝ :=
by
  apply himpl_antisym
  { move=> * ; sby apply hpure_intro_hempty }
  sby move=> ? []

lemma hfalse_hstar_any H :
  ⌜False⌝ ∗ H = ⌜False⌝ :=
by
  apply himpl_antisym
  { move=> ? ; sby srw hstar_hpure_l }
  move=> ? []
  sby srw hstar_hpure_l


/- ----------------- Properties of [hexists] ----------------- -/

lemma hexists_intro A (x : A) (J : A → hProp) h :
  J x h → (hexists J) h :=
by sdone

lemma hexists_inv A (J : A → hProp) h :
  (hexists J) h → exists x, J x h :=
by
  sby srw hexists

lemma himpl_hexists_l A H (J : A → hProp) :
  (forall x, J x ==> H) → (hexists J) ==> H :=
by
  srw [0](himpl)=> hJx ? [?]
  sby apply hJx

lemma himpl_hexists_r A (x : A) H (J : A → hProp) :
  (H ==> J x) →
  H ==> (hexists J) :=
by
  srw himpl=> * ??
  sby exists x

lemma himpl_hexists A (J1 J2 : A → hProp) :
  J1 ===> J2 →
  hexists J1 ==> hexists J2 :=
by
  srw qimpl=> hJs
  sby apply himpl_hexists_l=> ?? /hJs


/- ------------------- Properties of [hforall] ------------------- -/

lemma hforall_intro A (J : A → hProp) h :
  (forall x, J x h) → (hforall J) h :=
by sdone

lemma hforall_inv A (J : A → hProp) h :
  (hforall J) h → forall x, J x h :=
by
  sby srw hforall

lemma himpl_hforall_r A (J : A → hProp) H :
  (forall x, H ==> J x) →
  H ==> (hforall J) :=
by
  sby srw [0]himpl=> * ?

lemma himpl_hforall_l A (x : A) (J : A → hProp) H :
  (J x ==> H) →
  (hforall J) ==> H :=
by
  srw himpl=> ??
  sby srw hforall

lemma hforall_specialize A (x : A) (J : A → hProp) :
  (hforall J) ==> (J x) :=
by
  move=> ? ; sapply

lemma himpl_hforall A (J1 J2 : A → hProp) :
  J1 ===> J2 →
  hforall J1 ==> hforall J2 :=
by
  srw qimpl=> hQimp
  apply himpl_hforall_r=> ?
  apply himpl_hforall_l
  move: hQimp ; sapply


/- -------------------- Properties of [hwand] -------------------- -/

lemma hwandE :
  H1 -∗ H2 = hexists (fun H0 => H0 ∗ hpure ((H1 ∗ H0) ==> H2)) := rfl

lemma hwand_equiv H0 H1 H2 :
  (H0 ==> H1 -∗ H2) ↔ (H1 ∗ H0 ==> H2) :=
by
  srw hwandE ; apply Iff.intro
  { srw hstar_comm=> ?
    apply himpl_hstar_trans_l=>//
    srw hstar_hexists
    apply himpl_hexists_l=> ?
    srw [2](hstar_comm) (hstar_assoc) [2](hstar_comm)
    sby apply himpl_hstar_hpure_l }
  move=> ?
  apply himpl_hexists_r
  rw [<-hstar_hempty_r H0]
  apply himpl_frame_r ; sby apply himpl_hempty_hpure

lemma himpl_hwand_r H1 H2 H3 :
  H2 ∗ H1 ==> H3 →
  H1 ==> (H2 -∗ H3) :=
by
  sby srw hwand_equiv

lemma himpl_hwand_r_inv H1 H2 H3 :
  H1 ==> (H2 -∗ H3) →
  H2 ∗ H1 ==> H3 :=
by
  sby srw -hwand_equiv

lemma hwand_cancel H1 H2 :
  H1 ∗ (H1 -∗ H2) ==> H2 :=
by
  sby apply himpl_hwand_r_inv=> ?

lemma himpl_hempty_hwand_same H :
  emp ==> (H -∗ H) :=
by
  apply himpl_hwand_r
  sby srw hstar_hempty_r=> h

lemma hwand_hempty_l H :
  (emp -∗ H) = H :=
by
  apply himpl_antisym
  { rw [<- hstar_hempty_l (emp -∗ H)]
    apply hwand_cancel }
  apply himpl_hwand_r
  sby srw hstar_hempty_l=> ?

lemma hwand_hpure_l P H :
  P → (⌜P⌝ -∗ H) = H :=
by
  move=> ? ; apply himpl_antisym
  { apply himpl_trans
    apply (himpl_hstar_hpure_r P (⌜P⌝ -∗ H) (⌜P⌝ -∗ H))=>//
    apply himpl_refl
    apply hwand_cancel }
  srw hwand_equiv
  sby apply himpl_hstar_hpure_l=> ??

lemma hwand_curry H1 H2 H3 :
  (H1 ∗ H2) -∗ H3 ==> H1 -∗ (H2 -∗ H3) :=
by
  sdo 2 apply himpl_hwand_r;
  srw -hstar_assoc [0]hstar_comm
  apply hwand_cancel

lemma hwand_uncurry H1 H2 H3 :
  H1 -∗ (H2 -∗ H3) ==> (H1 ∗ H2) -∗ H3 :=
by
  srw hwand_equiv [2]hstar_comm hstar_assoc
  apply himpl_hstar_trans_r
  sdo 2 apply hwand_cancel;

lemma hwand_curry_eq H1 H2 H3 :
  (H1 ∗ H2) -∗ H3 = H1 -∗ (H2 -∗ H3) :=
by
  apply himpl_antisym
  { apply hwand_curry }
  apply hwand_uncurry

lemma hwand_inv h1 h2 H1 H2 :
  (H1 -∗ H2) h2 →
  H1 h1 →
  Finmap.Disjoint h1 h2 →
  H2 (h1 ∪ h2) :=
by
  move=> [? ![hW1 ?? [/himpl h1W hW2emp] ? /hW2emp /Finmap.union_empty hU *]]
  apply h1W ; exists h1, hW1
  sby srw hU


/- ----------------- Properties of [qwand] ----------------- -/

lemma qwandE α (Q1 Q2 : α → hProp) :
  Q1 -∗ Q2 = hforall (fun x => (Q1 x) -∗ (Q2 x)) := rfl

lemma qstarE α (Q1 : α → hProp)  (H : hProp):
  Q1 ∗ H = fun x => Q1 x ∗ H := rfl

lemma qwand_equiv H A (Q1 Q2 : A → hProp) :
  H ==> (Q1 -∗ Q2) ↔ (Q1 ∗ H) ===> Q2 :=
by
  srw qwandE ; apply Iff.intro
  { move=> ? x
    srw qstarE hstar_comm
    apply (himpl_hstar_trans_l H (hforall fun x' ↦ Q1 x' -∗ Q2 x'))=>//
    apply (himpl_trans (hforall fun x0 ↦ ((Q1 x0 -∗ Q2 x0) ∗ Q1 x)))
    apply hstar_hforall ; apply himpl_hforall_l
    rw [hstar_comm] ; apply hwand_cancel }
  srw qimpl qstarE => ?
  apply himpl_hforall_r => ?
  sby srw hwand_equiv=> ?

lemma qwand_cancel A (Q1 Q2 : A → hProp) :
  Q1 ∗ (Q1 -∗ Q2) ===> Q2 :=
by
  sby srw -qwand_equiv=> ?

lemma himpl_qwand_r A (Q1 Q2 : A → hProp) H :
  Q1 ∗ H ===> Q2 →
  H ==> (Q1 -∗ Q2) :=
by
  sby srw qwand_equiv

lemma qwand_specialize A (x : A) (Q1 Q2 : A → hProp) :
  (Q1 -∗ Q2) ==> (Q1 x -∗ Q2 x) :=
by
  sby apply (himpl_hforall_l A x)=> ?; sapply


/- --------------------- Properties of [htop] --------------------- -/

lemma htop_intro h :
  ⊤ h :=
by sdone

lemma himpl_htop_r H :
  H ==> ⊤ :=
by sdone

lemma htop_eq :
  ⊤ = h∃ H, H :=
by
  srw htop

lemma hstar_htop_htop :
  ⊤ ∗ ⊤ = ⊤ :=
by
  apply himpl_antisym
  { apply himpl_htop_r }
  srw -[1](hstar_hempty_r ⊤)
  apply himpl_frame_r ; apply himpl_htop_r


/- -------------------- Properties of [hsingle] -------------------- -/

lemma hsingle_intro p v :
  (p ~~> v) (Finmap.singleton p v) :=
by sdone

lemma hsingl_inv p v h :
  (p ~~> v) h →
  h = Finmap.singleton p v :=
by sapply

lemma disjoint_single_same_inv {α : Type u} {β : α → Type v}
  (p : α) (v1 v2 : β p) :
  Finmap.Disjoint (Finmap.singleton p v1) (Finmap.singleton p v2) →
  False :=
by
  sby srw Finmap.Disjoint Not => ?


lemma hstar_hsingle_same_loc p v1 v2 :
  (p ~~> v1) ∗ (p ~~> v2) ==> ⌜False⌝ :=
by
  move=> ? ![??]
  srw [0]hsingle => hh1 hh2 /hh1 /hh2 hDisj ?
  srw (hpure) (hexists) /==
  apply (disjoint_single_same_inv p v1 v2 hDisj)


/- -------- Definitions and Properties of [haffine] and [hgc] -------- -/

def haffine (_ : hProp) :=
  True

lemma haffine_hany : forall H,
  haffine H :=
by sdone

lemma haffine_hempty : haffine emp := haffine_hany emp

def hgc := htop -- Equivalent to [exists H, /[haffine H] ∗ H]

notation "/GC" => hgc

lemma haffine_hgc : haffine /GC := haffine_hany /GC

lemma himpl_hgc_r : forall H,
  haffine H →
  H ==> /GC :=
by
  sby move=> * ?

lemma hstar_hgc_hgc : /GC ∗ /GC = /GC := hstar_htop_htop


/- ------------------- Instantiate [xsimpl] ------------------- -/


/- ------------------ Properties of [haffine] ------------------ -/

lemma haffine_hpure P :
  haffine ⌜P⌝ :=
by
  apply haffine_hany

lemma haffine_hstar H1 H2 :
  haffine H1 → haffine H2 → haffine (H1 ∗ H2) :=
by
  move=> * ; apply haffine_hany

lemma haffine_hexists A (J : A → hProp) :
  (forall x, haffine (J x)) →
  haffine (hexists J) :=
by
  move=> * ; apply haffine_hany

lemma haffine_hforall A {_ : Inhabited A} (J : A → hProp) :
  (forall x, haffine (J x)) →
  haffine (hforall J) :=
by
  move=> * ; apply haffine_hany

lemma haffine_hastar_hpure (P : Prop) H :
  (P → haffine H) →
  haffine (⌜P⌝ ∗ H) :=
by
  move=> * ; apply haffine_hany


/- ------------- Definition and properties of [placeholder] ------------- -/

def hind : hProp :=
  hexists (fun b ↦ if b then emp else ⊤)

notation:max "⊤⊤" => hind

lemma hind_any h : ⊤⊤ h :=
by
  sby exists false

lemma hind_hstar_hempty :
  ⊤⊤ ∗ emp ==> ⊤⊤ :=
by
  move=> *
  sby apply hind_any


open HStar HWand

/- TODO: Add more properties -/