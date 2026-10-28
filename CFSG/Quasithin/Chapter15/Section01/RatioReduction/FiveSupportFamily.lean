module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.FiveSupportFamily
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SelectedAction

/-!
# Quintic support bounds for the selected local action

The original local subgroup covers its literal conjugation image. Its
SQTK prime-rank bound limits the canonical quintic support family to two,
while every original starred actor normalizes each support. This removes
the rank premise in the second paragraph of 15.1.2 without using a rank
bound on an arbitrary quotient or changing the starred family.

Source: Aschbacher--Smith 15.1.2, printed p.1084.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06 Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The literal image of the original local subgroup supplies the quintic
rank bound and preserves all original starred actors. -/
theorem source_localAction_five_support_family
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let := BinaryGroupAction.action ρ
    ∀ A : Subgroup D, A ∈ QhatStar ρ → rank A = 1 → ⁅pCore 5 D,A⁆ ≠ ⊥ →
      cubicRatio ρ = 2 ∧
      (∀ X ∈ smallSupportFactors D (Multiplicative (Additive (localModule T M))) 2,
        Jhat ρ ≤ normalizer (X : Set D)) ∧
      Nat.card (smallSupportFactors D (Multiplicative (Additive (localModule T M))) 2) ≤ 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let f := actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let := BinaryGroupAction.action ρ
  dsimp only
  intro A hA hr hm
  have hf := imageRepresentation_injective M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  have hq := (source_lemma_D_2_13_cyclic_five ρ hf hA hr hm).1
  refine ⟨hq,fiveSupport_Jhat_le_normalizer ρ hf hq,?_⟩
  exact five_core_canonical_family_bound ρ hf f.rangeRestrict f.rangeRestrict_surjective
    ((Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1)).stronglyQuasithin
      5 (by decide) (by decide)) hA hr hm
end CFSG.Quasithin.Chapter15.Section01
