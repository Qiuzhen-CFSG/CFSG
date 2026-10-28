module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Candidates
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.Representatives
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.NormalizerInclusions.Middle
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.NormalizerInclusions.RankFour

/-!
# Placement of the four literal outer Held normalizers

The first three rows are placed in a fixed conjugate of the full max5
normalizer. The rank-four row has full normalizer in Held equal to the actual
pure-pair product, as proved in `NormalizerInclusions.RankFour`. Any
automorphism preserving a subgroup preserves its full inner normalizer, so
this identity supplies the full outer inclusion and retains the outer actors
that interchange the max3/max4 classes.

The four inclusions require only full permutation realization. They discharge
the normalizer-placement input of the separate local-cover assembly.
Enumeration of normal elementary subgroups and local characteristic two
remain separate tasks; neither is assumed here.
Source: Aschbacher--Smith 15.3.41--42, printed p.1138; GLS3 Table 5.3p.
-/

public section
open Subgroup Held.LocalPairs
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
open CoverageData

/-- The full outer inclusion follows from the exact inner normalizer identity. -/
theorem ambientRow_three_normalizer_le_of_inner_identity
    (hfour : normalizer (heldRow 3 : Set Held.He) = innerLocal true) :
    normalizer (ambientRow 3 : Set (MulAut Held.He)) ≤ candidate true := by
  rw [NormalizerInclusions.ambientRow_normalizer]
  have h := NormalizerInclusions.automorphismNormalizer_le_innerNormalizer (heldRow 3)
  rw [hfour] at h
  exact h

/-- Assembly from a supplied rank-four inner identity. The concrete identity
is discharged in `four_normalizer_inclusions` below. -/
theorem four_normalizer_inclusions_of_rankFour_inner_normalizer
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hfour : normalizer (heldRow 3 : Set Held.He) = innerLocal true) :
    ∀ j : Fin 4, ∃ (i : Bool) (g : MulAut Held.He),
      normalizer (ambientRow j : Set (MulAut Held.He)) ≤
        (candidate i).map (MulAut.conj g).toMonoidHom := by
  intro j
  fin_cases j
  · exact ⟨false, MulAut.conj NormalizerInclusions.rowZeroConjugator,
      NormalizerInclusions.ambientRow_zero_normalizer_le⟩
  · exact ⟨false, MulAut.conj NormalizerInclusions.rowZeroConjugator,
      NormalizerInclusions.ambientRow_middle_normalizer_le hreal 0⟩
  · exact ⟨false, MulAut.conj NormalizerInclusions.rowZeroConjugator,
      NormalizerInclusions.ambientRow_middle_normalizer_le hreal 1⟩
  · refine ⟨true, 1, ?_⟩
    have he : (MulAut.conj (1 : MulAut Held.He)).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [he, map_id]
    exact ambientRow_three_normalizer_le_of_inner_identity hfour

/-- The full automorphism normalizer of the fourth literal row preserves the
actual pure-pair product, including its outer max3/max4 interchange actors. -/
theorem ambientRow_three_normalizer_le :
    normalizer (ambientRow 3 : Set (MulAut Held.He)) ≤ candidate true :=
  ambientRow_three_normalizer_le_of_inner_identity
    NormalizerInclusions.heldRow_three_normalizer

/-- Placement of all four full ambient normalizers in the two literal candidates.
This supplies exactly the normalizer certificate used by the proper-extension
local cover, with no elementary-exhaustion, order, or local-shape premise. -/
theorem four_normalizer_inclusions
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom) :
    ∀ j : Fin 4, ∃ (i : Bool) (g : MulAut Held.He),
      normalizer (ambientRow j : Set (MulAut Held.He)) ≤
        (candidate i).map (MulAut.conj g).toMonoidHom :=
  four_normalizer_inclusions_of_rankFour_inner_normalizer hreal
    NormalizerInclusions.heldRow_three_normalizer

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
