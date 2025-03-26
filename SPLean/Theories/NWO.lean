import Lean.Elab.Tactic
import Qq

import SPLean.Theories.HProp
import SPLean.Common.Util


-- open hprop_scope
open Lean Lean.Expr Lean.Meta Qq
open Lean Elab Command Term Meta Tactic

/- [nwo] (No Wand Out) tactic implementation -/
inductive hprop : Type where
  | sep : List hprop -> hprop
  | pure : Expr -> hprop
  | emp : hprop
  | wand : hprop -> hprop -> hprop
  | exists : Name -> Expr -> hprop -> hprop
deriving Inhabited

partial def Lean.Expr.toHprop (e : Expr) : hprop :=
  match_expr e with
  | HStar.hStar _ _ _ _ h₁ h₂ => hprop.sep (go h₁ ++ go h₂)
  | HWand.hWand _ _ _ _ h₁ h₂ => hprop.wand h₁.toHprop h₂.toHprop
  | hpure p => hprop.pure p
  | hempty => hprop.emp
  | hexists _ j =>
    match j.consumeMData with
    | forallE n tp bd _ => hprop.exists n tp bd.toHprop
    | _ => panic! s!"{j} is not a valid existential quantifier"
  | _ => panic! s!"{e} is not handled yet"
  where
go (e : Expr) : List hprop :=
  match_expr e with
  | HStar.hStar _ _ _ _ h₁ h₂ => go h₁ ++ go h₂
  | _ => [e.toHprop]

structure NWOState where
  pures : List Expr
  ----
  hla : hprop
  hlw : hprop
  hlt : hprop
  ----
  hra : hprop
  hrw : hprop
  hrt : hprop

-- Get the symbolic state from the goal
def getEntailment : TacticM NWOState := sorry
