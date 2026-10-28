module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionFusion.Data
import Mathlib.Tactic.FinCases

/-!
# Checked fusion of the outer Hall--Janko Sylow involutions

The finite check covers every element in the outer coset of the fixed Sylow
subgroup. Each involution is conjugate, by a word in the original carrier,
to the displayed normalizing involution. Every permutation equality is
kernel checked. Source: GLS3, Table 5.3g, class 2C; retained ATLAS J2G1-p100B0.
-/

public section
namespace Sporadic.LeechRelated.J2.OuterInvolutionFusion
open Theory.GroupTheory GeneratorPair ExceptionalParabolics
open PairNormalizer PairNormalizer.SylowData SecondParabolic
open GeneratorPair.SecondOrbitCertificate

set_option maxRecDepth 100000 in
private theorem fusion_check : ∀ i : Fin 128,
    (sTable i * outerTable) ^ 2 = 1 →
    evalWord ![tableA, tableB, tableB⁻¹] (conjugatorWord i) * involution *
      (evalWord ![tableA, tableB, tableB⁻¹] (conjugatorWord i))⁻¹ =
        sTable i * outerTable := by
  apply allFin
  decide +kernel

private theorem localWord_inclusion (w : List (Fin 3)) :
    inclusion (Seed.localWord w) = evalWord ![tableA, tableB, tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion (![a, b, b⁻¹] i * Seed.localWord w) = _
    rw [map_mul, ih]
    congr 1
    fin_cases i <;> simp [a, b, inclusion, generatorA_eq_table, generatorB_eq_table]

/-- Every involution in the outer Sylow coset has a checked inner conjugator. -/
theorem sylow_coset_fusion (i : Fin 128)
    (hi : (intoExtension (sElement i) * Seed.outerElement) ^ 2 = 1) :
    IsConj extensionInvolution (intoExtension (sElement i) * Seed.outerElement) := by
  apply isConj_iff.mpr
  refine ⟨intoExtension (Seed.localWord (conjugatorWord i)), ?_⟩
  apply extension.subtype_injective
  have hsq := congrArg extension.subtype hi
  simp only [map_pow, map_mul, map_one, outerElement_inclusion] at hsq
  change (inclusion (sElement i) * outerTable) ^ 2 = 1 at hsq
  rw [sElement_inclusion] at hsq
  simp only [map_mul, map_inv, outerElement_inclusion]
  change inclusion (Seed.localWord (conjugatorWord i)) * involution *
    (inclusion (Seed.localWord (conjugatorWord i)))⁻¹ =
      inclusion (sElement i) * outerTable
  rw [localWord_inclusion, sElement_inclusion]
  exact fusion_check i hsq

end Sporadic.LeechRelated.J2.OuterInvolutionFusion
