import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun

import Lgtm.Experiments.UnaryCommon


open Unary prim val trm

namespace Lang
notation "arr⟨"s"⟩(" p "," x " in " n " => " f ")" => hharrayFun s (fun x => f) n (fun _ => p)

lemma findIdx_hspec (l : ℕ) (f : ℤ -> ℝ) (target : Labeled α -> ℝ) (s : Set α)
  (z n : ℤ) (_ : z <= n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  Set.InjOn f ⟦z, n⟧ ->
  (∀ i ∈ ⟪l,s⟫, target i ∈ f '' ⟦z, n⟧) ->
  arr⟨⟪l,s⟫⟩(arr, x in N => f x) ==>
    hwp ⟪l, s⟫ (fun i ↦ [lang| findIdx arr ⟨target i⟩ z n])
    fun v ↦ ⌜v = fun i ↦ val_int (f.invFunOn ⟦z, n⟧ (target i))⌝ ∗ arr⟨⟪l, s⟫⟩(arr, x in N => f x) := by
  move=> ??
  apply htriple_prod_val_eq=> [] /== ? i ??
  xapp findIdx_spec; xsimp=> //

lemma findIdx_hspec_out (l : ℕ) (f : ℤ -> ℝ) (target : Labeled α -> ℝ) (s : Set α)
  (z n : ℤ) (_ : z <= n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  Set.InjOn f ⟦z, n⟧ ->
  (∀ i ∈ ⟪l,s⟫, target i ∉ f '' ⟦z, n⟧) ->
  arr⟨⟪l,s⟫⟩(arr, x in N => f x) ==>
     hwp ⟪l, s⟫ (fun i ↦ [lang| findIdx arr ⟨target i⟩ z n]) fun v ↦ ⌜v = fun _ ↦ val_int $ n⌝ ∗ arr⟨⟪l, s⟫⟩(arr, x in N => f x) := by
  move=> ??
  apply htriple_prod_val_eq=> [] /== ? i ??
  xapp findIdx_spec_out

@[yapp]
lemma or_eq_hspec (a b : α -> Bool) (p : α -> loc) :
  (p i ~⟨i in s⟩~> a i) ==>
    hwp s (fun i => trm_app val_or_eq (p i) (b i)) (fun _ => p i ~⟨i in s⟩~> (b i || a i)) := by
  apply htriple_prod (Q := fun i _ => p i ~~> (b i || a i))=> ??; apply or_eq_spec

@[yapp]
lemma add_eq_hspec (a b : α -> ℝ) (p : α -> loc) :
  (p i ~⟨i in s⟩~> a i) ==>
    hwp s (fun i => trm_app val_add_eq (p i) (b i)) (fun _ => p i ~⟨i in s⟩~> (b i + a i)) := by
  apply htriple_prod (Q := fun i _ => p i ~~> (b i + a i))=> ??; apply add_eq_spec

@[yapp]
lemma and_hspec (a b : α -> Bool) :
  emp ==>
    hwp s (fun i => trm_app val_and (a i) (b i)) (fun v => ⌜v = fun i => val_bool (a i && b i)⌝) := by
  apply htriple_prod_val_eq_emp => ??; apply and_spec

lemma searchIdx_hspec (l : ℕ) (f : ℤ -> ℝ) (s : Set ℝ)
  (z n : ℤ) (_ : z < n) (_ : 0 <= z) (N : ℕ) (_ : n < N) :
  MonotoneOn f ⟦z, n+1⟧ ->
  i ∈ ⟦z, n⟧ ->
  (s ⊆ Set.Ico (f i) (f (i+1)))->
  arr⟨⟪l,s⟫⟩(arr, x in N => f x) ==>
    hwp ⟪l, s⟫ (fun i ↦ [lang| searchIdx arr ⟨i.val⟩ z ⟨n+1⟩])
    fun v ↦ ⌜v = fun _ ↦ val_int i⌝ ∗ arr⟨⟪l, s⟫⟩(arr, x in N => f x) := by
  move=> ???
  apply htriple_prod_val_eq=> [] /== ? j ??
  xapp searchIdx_spec'

lemma searchSRLE_hspec (l : ℕ) (lf rf : ℤ -> ℝ) (s : Set ℝ)
  (z n : ℤ) (_ : z < n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  (∀ i ∈ ⟦z, n⟧, lf i <= rf i) ->
  (∀ i ∈ ⟦z, n-1⟧, rf i <= lf (i + 1)) ->
  i ∈ ⟦z, n⟧ ->
  (s ⊆ Set.Ico (lf i) (rf i))->
  arr⟨⟪l,s⟫⟩(left, x in N => lf x) ∗ arr⟨⟪l,s⟫⟩(right, x in N => rf x) ==>
    hwp ⟪l, s⟫ (fun i ↦ [lang| searchSRLE left right ⟨i.val⟩ z n])
    fun v ↦ ⌜v = fun _ ↦ val_int i⌝ ∗ arr⟨⟪l,s⟫⟩(left, x in N => lf x) ∗ arr⟨⟪l,s⟫⟩(right, x in N => rf x) := by
  move=> ????
  srw ?hharrayFun bighstar_hhstar
  apply htriple_prod_val_eq=> [] /== ? j ??
  xapp searchSparseRLE_spec'

lemma searchSRLE_hspec_out (l : ℕ) (lf rf : ℤ -> ℝ) (s : Set ℝ)
  (z n : ℤ) (_ : z < n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  (∀ i ∈ ⟦z, n⟧, lf i <= rf i) ->
  (∀ i ∈ ⟦z, n-1⟧, rf i <= lf (i + 1)) ->
  Disjoint s (⋃ i ∈ ⟦z, n⟧, Set.Ico (lf i) (rf i)) ->
  arr⟨⟪l,s⟫⟩(left, x in N => lf x) ∗ arr⟨⟪l,s⟫⟩(right, x in N => rf x) ==>
    hwp ⟪l, s⟫ (fun i ↦ [lang| searchSRLE left right ⟨i.val⟩ z n])
    fun v ↦ ⌜v = fun _ ↦ val_int n⌝ ∗ arr⟨⟪l,s⟫⟩(left, x in N => lf x) ∗ arr⟨⟪l,s⟫⟩(right, x in N => rf x) := by
  move=> ?? /Set.disjoint_left ?
  srw ?hharrayFun bighstar_hhstar
  apply htriple_prod_val_eq=> [] /== ? j ??
  xapp searchSparseRLE_spec_out


end Lang
