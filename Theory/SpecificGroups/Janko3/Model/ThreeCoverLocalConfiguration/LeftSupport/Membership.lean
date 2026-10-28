module

public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.LeftSupport.Conjugator
public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Elements.X
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0

/-!
# Membership of the marked scalar in the J₃ left support

The literal word `conjugator⁻¹ * x * conjugator` equals a word in the five
centralizer generators. Checking this identity on all 6156 letters proves
membership in the conjugated support with the precise conjugation convention
of `Words.lean`. The witness is the second entry in `source/local-words.json`.
Source: GLS3, Table 5.3h, printed p.269; Aschbacher--Smith A.2.19, p.41.
-/

namespace Sporadic.Janko3.ThreeCoverConfig
open Theory.GroupTheory OrderCertificate TwoLocal TwoLocal.CentralizerCertificate
open LeftSupportCertificate
set_option maxRecDepth 40000
set_option Elab.async false

set_option maxHeartbeats 4000000 in
private theorem scalar_conjugate_word :
    conjugator⁻¹ * x * conjugator =
      centralizerGenerator 2 * centralizerGenerator 3 ^ 2 * centralizerGenerator 4 *
        (centralizerGenerator 2)⁻¹ * (centralizerGenerator 0)⁻¹ * centralizerGenerator 3 := by
  apply Subtype.ext
  change (conjugator : Equiv.Perm (Fin 6156))⁻¹ * (x : Equiv.Perm (Fin 6156)) *
      (conjugator : Equiv.Perm (Fin 6156)) =
    (centralizerGenerator 2 : Equiv.Perm (Fin 6156)) *
      (centralizerGenerator 3 : Equiv.Perm (Fin 6156)) ^ 2 *
      (centralizerGenerator 4 : Equiv.Perm (Fin 6156)) *
      (centralizerGenerator 2 : Equiv.Perm (Fin 6156))⁻¹ *
      (centralizerGenerator 0 : Equiv.Perm (Fin 6156))⁻¹ *
      (centralizerGenerator 3 : Equiv.Perm (Fin 6156))
  rw [← conjugatorPerm_eq, ← xPerm_eq, ← C0G2_eq_generator, ← C0G3_eq_generator,
    ← C0G4_eq_generator, ← C0G0_eq_generator]
  apply Equiv.ext
  apply allLetters
  decide +kernel

/-- The marked scalar belongs to the literal conjugate of the centralizer candidate. -/
public theorem x_mem_leftSupport : x ∈ leftSupport := by
  have hx : conjugator⁻¹ * x * conjugator ∈ centralizerCandidate := by
    rw [scalar_conjugate_word]
    exact centralizerCandidate.mul_mem
      (centralizerCandidate.mul_mem
        (centralizerCandidate.mul_mem
          (centralizerCandidate.mul_mem
            (centralizerCandidate.mul_mem (centralizerGenerator_mem 2)
              (centralizerCandidate.pow_mem (centralizerGenerator_mem 3) 2))
            (centralizerGenerator_mem 4))
          (centralizerCandidate.inv_mem (centralizerGenerator_mem 2)))
        (centralizerCandidate.inv_mem (centralizerGenerator_mem 0)))
      (centralizerGenerator_mem 3)
  apply Subgroup.mem_map.mpr
  refine ⟨conjugator⁻¹ * x * conjugator, hx, ?_⟩
  change conjugator * (conjugator⁻¹ * x * conjugator) * conjugator⁻¹ = x
  simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right]

end Sporadic.Janko3.ThreeCoverConfig
