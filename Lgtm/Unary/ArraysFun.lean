import Lgtm.Unary.XSimp
import Lgtm.Unary.XChange
import Lgtm.Unary.Util
import Lgtm.Unary.SepLog
import Lgtm.Unary.WP1
import Lgtm.Unary.Lang
import Lgtm.Unary.Arrays

open Classical

/- ============== Definitions for Arrays represented ans funtions ============== -/

open trm val Unary

def harrayFun (f : ℤ -> val) (n : ℕ) (p : loc) : hProp :=
  harray (@List.ofFn _ n (f ·)) p

attribute [-simp] Int.natCast_natAbs

notation "arr(" p ", " x " in " n " => " f ")" => harrayFun (fun x => f) n p

lemma triple_harrayFun_get (p : loc) (i : Int) :
   0 <= i ∧ i < (n : ℕ) →
   triple (trm_app val_array_get p i)
    (harrayFun f n p)
    (fun r ↦ ⌜r = f i⌝ ∗ harrayFun f n p) := by
  move=> ?
  xapp triple_array_get; xsimp
  srw getElem!_pos /== <;> try omega
  srw List.getElem_ofFn /==; congr!; omega

lemma triple_harrayFun_set (f : ℤ -> val) (p : loc) (i : Int) (v : val) :
   0 <= i ∧ i < (n : ℕ) →
   triple (trm_app val_array_set p i v)
    (harrayFun f n p)
    (fun _ => harrayFun (Function.update f i v) n p) := by
  move=> ?
  xapp triple_array_set; xsimp
  shave->//: (@List.ofFn _ n fun x ↦ f x).set i.natAbs v =
          @List.ofFn _ n ((Function.update f i v) ·)
  { apply List.ext_getElem=> //== ???
    srw List.getElem_set /== Function.update /==
    scase_if=> ?
    { srw if_pos; omega }
    srw if_neg; omega }
  apply himpl_refl