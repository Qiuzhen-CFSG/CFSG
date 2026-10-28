module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.CoordinateMap

/-!
# Permutation identities used in the generator comparison

The diagonal and flip permutations give the even and odd automorphism
collection identities on the actual `Option ParkerLoop` triples. Rotation of
coordinates gives the second-family inverse identity; explicit sign actions
give the remaining identities used in the conjugation calculation.

The private collection proofs are adapted from the project's
`Structure/NormalForms/Collection/WordClosure.lean`, preserving that module's
public boundary. No alternate triple model or lattice action is used.
Source: Aschbacher, *Sporadic Groups*, Lemma 14.2, printed pp. 58–60.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer
namespace Sporadic.Monster.Construction.LocalC.TrialityGeneratorCalculation
open TrialitySpin

-- The collection proofs below are reproduced from WordClosure, whose helpers
-- are private, to preserve that existing module's public boundary.
private theorem inverse_product (d e : ParkerLoop) :
    loopInverse (parkerLoopMultiply d e) =
      parkerLoopMultiply (loopInverse e) (loopInverse d) := by
  rw [loopInverse, loopInverse, loopInverse, parkerLoopMultiply_sign_left,
    parkerLoopMultiply_sign_right, parkerLoopMultiply_commutator e d,
    parkerSign_add, parkerSign_add]
  change parkerSign (golayQuarterWeight (d.1 + e.1)) _ = _
  rw [golayQuarterWeight_add, golayHalfOverlap_symmetric e.1 d.1,
    add_comm (golayQuarterWeight d.1) (golayQuarterWeight e.1)]

private theorem diagonal_mul (α β : ParkerStandardGroup) :
    diagonal (α * β).val = diagonal α.val * diagonal β.val := by
  ext ⟨a,b,c⟩ : 1
  cases a <;> cases b <;> cases c <;> rfl

private theorem diagonal_flip (α : ParkerStandardGroup) :
    diagonal α.val * flip1 = flip1 * diagonal α.val := by
  ext ⟨a,b,c⟩ : 1
  have hi (a : LoopZero) : (inverseZero a).map α.val = inverseZero (a.map α.val) := by
    cases a with
    | none => rfl
    | some a => exact congrArg some (parkerStandard_preserves_inverse α a)
  exact Prod.ext (hi a) (Prod.ext (hi c) (hi b))

private theorem flip_sq : flip1 * flip1 = 1 := by
  ext ⟨a,b,c⟩ : 1
  simp [flip1, Equiv.Perm.mul_apply]

private theorem even_mul_iff (α β : ParkerStandardGroup) :
    (α * β).val parkerOmega = parkerOmega ↔
      (α.val parkerOmega = parkerOmega ↔ β.val parkerOmega = parkerOmega) := by
  have hs : ∀ s : Bit, s = 0 ∨ s = 1 := by decide
  have h (γ : ParkerStandardGroup) :
      γ.val parkerOmega = parkerOmega ↔ (γ.val parkerOmega).2 = 0 :=
    (parkerStandardPlus_iff γ).symm
  rw [h, h, h]
  have hm := congrArg Multiplicative.toAdd (map_mul parkerStandardParity α β)
  change ((α * β).val parkerOmega).2 = (α.val parkerOmega).2 + (β.val parkerOmega).2 at hm
  rw [hm]
  rcases hs (α.val parkerOmega).2 with ha | ha <;>
    rcases hs (β.val parkerOmega).2 with hb | hb <;> simp [ha,hb]

theorem aut_mul (α β : ParkerStandardGroup) :
    psiAut1N (α * β) = psiAut1N α * psiAut1N β := by
  apply Subtype.ext
  change psiAut1 (α * β).val = psiAut1 α.val * psiAut1 β.val
  have ht (e : Equiv.Perm ParkerLoop) : flip1.trans (diagonal e) = diagonal e * flip1 := rfl
  simp only [psiAut1, ht, even_mul_iff]
  by_cases ha : α.val parkerOmega = parkerOmega <;>
    by_cases hb : β.val parkerOmega = parkerOmega <;>
    simp only [ha, hb, iff_true, iff_false, not_true_eq_false, ↓reduceIte, diagonal_mul]
  · rw [mul_assoc]
  · rw [mul_assoc, diagonal_flip, ← mul_assoc]
  · calc
      _ = diagonal α.val * (diagonal β.val * (flip1 * flip1)) := by rw [flip_sq, mul_one]
      _ = diagonal α.val * ((diagonal β.val * flip1) * flip1) := by rw [mul_assoc]
      _ = diagonal α.val * ((flip1 * diagonal β.val) * flip1) := by rw [diagonal_flip]
      _ = _ := by simp only [mul_assoc]

theorem aut_one : psiAut1N 1 = 1 := by
  apply Subtype.ext
  change psiAut1 (1 : ParkerStandardGroup).val = 1
  simp only [psiAut1, Subgroup.coe_one, Equiv.Perm.one_apply, ↓reduceIte]
  ext ⟨a,b,c⟩ : 1
  cases a <;> cases b <;> cases c <;> rfl

private theorem diagonal_left (α : ParkerStandardGroup) (d : ParkerLoop) (a : LoopZero) :
    (leftZero d a).map α.val = leftZero (α.val d) (a.map α.val) := by
  cases a with
  | none => rfl
  | some a => exact congrArg some (α.prop.1 d a)

private theorem diagonal_right (α : ParkerStandardGroup) (d : ParkerLoop) (a : LoopZero) :
    (rightZero d a).map α.val = rightZero (α.val d) (a.map α.val) := by
  cases a with
  | none => rfl
  | some a => exact congrArg some (α.prop.1 a d)

private theorem diagonal_psi1 (α : ParkerStandardGroup) (d : ParkerLoop) :
    diagonal α.val * psi1 d = psi1 (α.val d) * diagonal α.val := by
  ext ⟨a,b,c⟩ : 1
  simp only [Equiv.Perm.mul_apply, psi1_apply, diagonal, Equiv.prodCongr_apply, Prod.map_apply, Equiv.optionCongr_apply,
    diagonal_left, diagonal_right, parkerStandard_preserves_inverse]

private theorem diagonal_psi2 (α : ParkerStandardGroup) (d : ParkerLoop) :
    diagonal α.val * psi2 d = psi2 (α.val d) * diagonal α.val := by
  ext ⟨a,b,c⟩ : 1
  simp only [Equiv.Perm.mul_apply, psi2_apply, diagonal, Equiv.prodCongr_apply, Prod.map_apply, Equiv.optionCongr_apply,
    diagonal_left, diagonal_right, parkerStandard_preserves_inverse]

private theorem diagonal_psi3 (α : ParkerStandardGroup) (d : ParkerLoop) :
    diagonal α.val * psi3 d = psi3 (α.val d) * diagonal α.val := by
  ext ⟨a,b,c⟩ : 1
  simp only [Equiv.Perm.mul_apply, psi3_apply, diagonal, Equiv.prodCongr_apply, Prod.map_apply, Equiv.optionCongr_apply,
    diagonal_left, diagonal_right, parkerStandard_preserves_inverse]

private theorem inverse_left (d : ParkerLoop) (a : LoopZero) :
    inverseZero (leftZero d a) = rightZero (loopInverse d) (inverseZero a) := by
  cases a with
  | none => rfl
  | some a => exact congrArg some (inverse_product d a)

private theorem inverse_right (d : ParkerLoop) (a : LoopZero) :
    inverseZero (rightZero d a) = leftZero (loopInverse d) (inverseZero a) := by
  cases a with
  | none => rfl
  | some a => exact congrArg some (inverse_product a d)

private theorem sandwich_flexible (d : ParkerLoop) (a : LoopZero) :
    leftZero d (rightZero d a) = rightZero d (leftZero d a) := by
  cases a with
  | none => rfl
  | some a =>
    simp only [leftZero_some, rightZero_some]
    rw [parkerLoopMultiply_associator, parkerTripleIntersection_cycle,
      parkerTripleIntersection_cycle, parkerTripleIntersection_repeat, parkerSign_zero]

private theorem flip_psi1 (d : ParkerLoop) :
    flip1 * psi1 d = psi1 (loopInverse d) * flip1 := by
  ext ⟨a,b,c⟩ : 1
  simp only [Equiv.Perm.mul_apply, psi1_apply, flip1, Equiv.coe_fn_mk,
    inverse_left, inverse_right, loopInverse_inverse, sandwich_flexible]

private theorem flip_psi2 (d : ParkerLoop) :
    flip1 * psi2 d = psi3 (loopInverse d) * flip1 := by
  ext ⟨a,b,c⟩ : 1
  simp only [Equiv.Perm.mul_apply, psi2_apply, psi3_apply, flip1, Equiv.coe_fn_mk,
    inverse_left, inverse_right, loopInverse_inverse, sandwich_flexible]

private theorem flip_psi3 (d : ParkerLoop) :
    flip1 * psi3 d = psi2 (loopInverse d) * flip1 := by
  ext ⟨a,b,c⟩ : 1
  simp only [Equiv.Perm.mul_apply, psi2_apply, psi3_apply, flip1, Equiv.coe_fn_mk,
    inverse_left, inverse_right, loopInverse_inverse, sandwich_flexible]


theorem aut_psi1_even (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (d : ParkerLoop) :
    psiAut1N α * psi1N d = psi1N (α.val d) * psiAut1N α := by
  apply Subtype.ext
  change psiAut1 α.val * psi1 d = psi1 (α.val d) * psiAut1 α.val
  simpa only [psiAut1, if_pos hα] using diagonal_psi1 α d

theorem aut_psi2_even (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (d : ParkerLoop) :
    psiAut1N α * psi2N d = psi2N (α.val d) * psiAut1N α := by
  apply Subtype.ext
  change psiAut1 α.val * psi2 d = psi2 (α.val d) * psiAut1 α.val
  simpa only [psiAut1, if_pos hα] using diagonal_psi2 α d

theorem aut_psi3_even (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (d : ParkerLoop) :
    psiAut1N α * psi3N d = psi3N (α.val d) * psiAut1N α := by
  apply Subtype.ext
  change psiAut1 α.val * psi3 d = psi3 (α.val d) * psiAut1 α.val
  simpa only [psiAut1, if_pos hα] using diagonal_psi3 α d

theorem aut_psi1_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (d : ParkerLoop) :
    psiAut1N α * psi1N d = psi1N (α.val (loopInverse d)) * psiAut1N α := by
  apply Subtype.ext
  change psiAut1 α.val * psi1 d = psi1 (α.val (loopInverse d)) * psiAut1 α.val
  rw [psiAut1, if_neg hα]
  change diagonal α.val * flip1 * psi1 d = _
  rw [mul_assoc, flip_psi1, ← mul_assoc, diagonal_psi1, mul_assoc]
  rfl

theorem aut_psi2_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (d : ParkerLoop) :
    psiAut1N α * psi2N d = psi3N (α.val (loopInverse d)) * psiAut1N α := by
  apply Subtype.ext
  change psiAut1 α.val * psi2 d = psi3 (α.val (loopInverse d)) * psiAut1 α.val
  rw [psiAut1, if_neg hα]
  change diagonal α.val * flip1 * psi2 d = _
  rw [mul_assoc, flip_psi2, ← mul_assoc, diagonal_psi3, mul_assoc]
  rfl

theorem aut_psi3_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (d : ParkerLoop) :
    psiAut1N α * psi3N d = psi2N (α.val (loopInverse d)) * psiAut1N α := by
  apply Subtype.ext
  change psiAut1 α.val * psi3 d = psi2 (α.val (loopInverse d)) * psiAut1 α.val
  rw [psiAut1, if_neg hα]
  change diagonal α.val * flip1 * psi3 d = _
  rw [mul_assoc, flip_psi3, ← mul_assoc, diagonal_psi2, mul_assoc]
  rfl


private theorem rotate_psi1 (d : ParkerLoop) :
    MulAut.conj cycle (psi1 d) = psi2 d := by
  ext ⟨a,b,c⟩ : 1
  rfl

theorem psi2_inv (d : ParkerLoop) : (psi2N d)⁻¹ = psi2N (loopInverse d) := by
  have h := congrArg (fun g : N => MulAut.conj cycle g.val) (psi1N_inv d)
  apply Subtype.ext
  change (psi2 d)⁻¹ = psi2 (loopInverse d)
  simpa only [Subgroup.coe_inv, show (psi1N d).val = psi1 d from rfl,
    show (psi1N (loopInverse d)).val = psi1 (loopInverse d) from rfl,
    map_inv, rotate_psi1] using h

theorem psi2_sign (s : ParkerBit) (d : ParkerLoop) :
    psi2N (parkerSign s d) = psi2N (0,s) * psi2N d := by
  have hs : s = 0 ∨ s = 1 := by revert s; decide
  rcases hs with rfl | rfl
  · apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi2 (parkerSign 0 d) (a,b,c) = psi2 loopOne (psi2 d (a,b,c))
    simp
  · apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi2 (parkerSign 1 d) (a,b,c) = z2 (psi2 d (a,b,c))
    cases a <;> cases b <;> cases c <;>
      simp [loopInverse_sign,parkerLoopMultiply_sign_left,parkerLoopMultiply_sign_right,parkerSign_add]

theorem psi3_sign (s : ParkerBit) (d : ParkerLoop) :
    psi3N (parkerSign s d) = psi3N (0,s) * psi3N d := by
  have hs : s = 0 ∨ s = 1 := by revert s; decide
  rcases hs with rfl | rfl
  · apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi3 (parkerSign 0 d) (a,b,c) = psi3 loopOne (psi3 d (a,b,c))
    simp
  · apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi3 (parkerSign 1 d) (a,b,c) = z3 (psi3 d (a,b,c))
    cases a <;> cases b <;> cases c <;>
      simp [loopInverse_sign,parkerLoopMultiply_sign_left,parkerLoopMultiply_sign_right,parkerSign_add]

theorem psi1_one : psi1N loopOne = 1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  simp [psi1N]

theorem psi2_one : psi2N loopOne = 1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  simp [psi2N]

end Sporadic.Monster.Construction.LocalC.TrialityGeneratorCalculation
