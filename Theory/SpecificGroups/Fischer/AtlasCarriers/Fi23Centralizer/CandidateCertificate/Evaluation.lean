module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.FixedPointSetup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.SupportA
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.SupportB
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.AllPoints

/-!
# Identification of the certified Fi23 candidate map

The disjoint source cycles and their fixed complements identify the two lookup
maps with the literal ATLAS generators. The checked word and seventh-power
identities therefore identify the candidate map, retaining the left-action
convention. The remaining checks give square one and the exact coordinate image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
open AtlasCarriers
open Sporadic.Fischer.Fi22.KernelCertificate

private theorem checks_at (x : Fin 31671) :
    wordMap x = wMap x ∧ (wMap^[7]) x = cMap x ∧ cMap (cMap x) = x ∧
    (cMap x = x ↔ ImageData.pointIndex (ImageData.index x) = x) ∧
    (supportMaskA.testBit x.val = true ∨ aMap x = x) ∧
    (supportMaskB.testBit x.val = true ∨ bMap x = x) := by
  have h := pointCheck_all x
  have hcast : Fin.ofNat 31671 x.val = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)
  simp only [pointCheck, if_pos x.isLt, wordCheck, candidateCheck, involutionCheck,
    fixedCheck, generatorFixedCheckA, generatorFixedCheckB, hcast,
    Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hw, hc⟩, hi⟩, hf⟩, ha⟩, hb⟩
  exact ⟨hw, hc, hi, by simpa only [beq_iff_eq] using Bool.eq_iff_iff.mp hf, ha, hb⟩

/-- The numerical first-generator map has the exact source action. -/
theorem generatorA_apply (x : Fin 31671) : generatorA x = aMap x := by
  simp only [generatorA, permutationFromCycleBlocks, KernelCertificate.cyclesA_spec]
  apply CycleCheck.inverse_prod_eq KernelCertificate.cyclesA aMap supportA.nodup
  · simpa only [List.all_eq_true, decide_eq_true_eq] using actionA
  · intro y hy
    rw [supportA.mask_eq] at hy
    exact ((checks_at y).2.2.2.2.1).resolve_left (by simp [hy])

/-- The numerical second-generator map has the exact source action. -/
theorem generatorB_apply (x : Fin 31671) : generatorB x = bMap x := by
  simp only [generatorB, permutationFromCycleBlocks, KernelCertificate.cyclesB_spec]
  apply CycleCheck.inverse_prod_eq KernelCertificate.cyclesB bMap supportB.nodup
  · simpa only [List.all_eq_true, decide_eq_true_eq] using actionB
  · intro y hy
    rw [supportB.mask_eq] at hy
    exact ((checks_at y).2.2.2.2.2).resolve_left (by simp [hy])

private theorem wordMap_eq (x : Fin 31671) : wordMap x = inclusion word x := by
  simp only [wordMap, ← generatorA_apply, ← generatorB_apply, word, map_mul,
    pow_succ, pow_zero, Equiv.Perm.mul_apply]
  rfl

theorem word_apply (x : Fin 31671) : inclusion word x = wMap x :=
  (wordMap_eq x).symm.trans (checks_at x).1

/-- The checked seventh-power table is the actual candidate permutation. -/
theorem candidate_apply (x : Fin 31671) : inclusion candidate x = cMap x := by
  have hw : wMap = inclusion word := funext fun y => (word_apply y).symm
  have he : (wMap^[7]) x = inclusion candidate x := by
    simp only [hw, candidate, map_pow, Equiv.Perm.coe_pow]
  exact he.symm.trans (checks_at x).2.1

theorem cMap_involution (x : Fin 31671) : cMap (cMap x) = x :=
  (checks_at x).2.2.1

theorem cMap_fixed (x : Fin 31671) :
    cMap x = x ↔ ImageData.pointIndex (ImageData.index x) = x :=
  (checks_at x).2.2.2.1

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
