module

public import Theory.SpecificGroups.Janko3.Model.Order.FastGenerators
public import Mathlib.Algebra.Group.Conj

/-!
# Evaluating short conjugates of the standard J₃ involution

A binary word has terminal sentinel 1; its low bit chooses a or b and the
remaining bits encode the tail. A fuel bound makes evaluation elementary
structural recursion. Even a truncated code still defines an actual conjugate.
The fast point maps are previously kernel-checked copies of the ATLAS maps.
Their two-letter key is proved equal to the key of the actual model element.

Source: ATLAS J3G1-p6156B0; the involution centralizer in GLS3 Table 5.3h,
printed p.269. This module makes no order or centralizer assumption.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.InvolutionCertificate
open Sporadic.Janko3 Sporadic.Janko3.OrderCertificate

@[expose] public def wordConjugate : Nat → Nat → Model
  | 0, _ => a
  | n+1, w => if w < 2 then a else
    let s := if w % 2 = 0 then a else b
    s * wordConjugate n (w / 2) * s⁻¹

public theorem wordConjugate_isConj (n w : Nat) : IsConj a (wordConjugate n w) := by
  induction n generalizing w with
  | zero => exact IsConj.refl _
  | succ n ih =>
    rw [wordConjugate]
    split
    · exact IsConj.refl _
    · exact (ih _).trans (isConj_iff.mpr ⟨_, rfl⟩)

@[expose] public def wordPoint : Nat → Nat → Fin 6156 → Fin 6156
  | 0, _, x => fastAMap x
  | n+1, w, x => if w < 2 then fastAMap x else
      if w % 2 = 0 then fastAMap (wordPoint n (w/2) (fastAInvMap x))
      else fastBMap (wordPoint n (w/2) (fastBInvMap x))

public theorem wordPoint_spec (n w : Nat) (x : Fin 6156) :
    wordPoint n w x = embedding (wordConjugate n w) x := by
  have hA (x) : fastAMap x = atlasA x :=
    congrArg (fun g : Equiv.Perm (Fin 6156) => g x) fastA_eq_atlas
  have hB (x) : fastBMap x = atlasB x :=
    congrArg (fun g : Equiv.Perm (Fin 6156) => g x) fastB_eq_atlas
  have hAi (x) : fastAInvMap x = (atlasA⁻¹) x :=
    congrArg (fun g : Equiv.Perm (Fin 6156) => g.symm x) fastA_eq_atlas
  have hBi (x) : fastBInvMap x = (atlasB⁻¹) x :=
    congrArg (fun g : Equiv.Perm (Fin 6156) => g.symm x) fastB_eq_atlas
  induction n generalizing w x with
  | zero => exact hA x
  | succ n ih =>
    simp only [wordPoint, wordConjugate]
    split
    · exact hA x
    · split <;> simp only [ih, hA, hB, hAi, hBi] <;> rfl

@[expose] public def wordKey (w : Nat) : Nat :=
  (wordPoint 30 w 0).val + 8192 * (wordPoint 30 w 1).val

@[expose] public def modelKey (g : Model) : Nat :=
  (embedding g 0).val + 8192 * (embedding g 1).val

public theorem wordKey_spec (w : Nat) : wordKey w = modelKey (wordConjugate 30 w) := by
  simp only [wordKey, modelKey, wordPoint_spec]

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.InvolutionCertificate
