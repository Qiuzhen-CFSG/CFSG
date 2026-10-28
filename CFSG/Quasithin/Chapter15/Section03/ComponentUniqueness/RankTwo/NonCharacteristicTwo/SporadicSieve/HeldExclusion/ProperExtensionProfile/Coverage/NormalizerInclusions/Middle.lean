module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.NormalizerInclusions.Middle.Checks

/-!
# Full ambient normalizers of the two middle Held rows

The checked finite signatures uniquely recognize the first row's involution
in both middle rows. Full permutation realization makes these signatures
invariant under every automorphism preserving a row. Thus both full ambient
normalizers preserve the first row and lie in its actual max5 conjugate.

This proves inclusions only; exact normalizer orders are unnecessary. Source:
Aschbacher--Smith 15.3.41--42, printed p.1138, and GLS3 Table 5.3p.
-/

@[expose] public section
open Subgroup Held.LocalPairs
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.NormalizerInclusions
open CoverageData
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment (commonFixedCount)
namespace Middle

def Signature (k : Fin 2) (x : Held.He) : Prop :=
  x ∈ heldRow (rowIndex k) ∧ commonFixedCount x x = 42 ∧
    ∀ y ∈ heldRow (rowIndex k), commonFixedCount x y ≠ 10

theorem central_signature (k : Fin 2) : Signature k rowZeroElement := by
  refine ⟨normalForm_central k ▸ normalForm_mem k (centralIndex k), ?_, ?_⟩
  · rw [← normalForm_central k, normal_count_eq]
    exact central_count_check k
  · intro y hy
    obtain ⟨i, rfl⟩ := normalForm_cover k hy
    rw [← normalForm_central k, normal_count_eq]
    exact central_avoid_check k i

theorem signature_unique (k : Fin 2) (x : Held.He) (hx : Signature k x) : x = rowZeroElement := by
  obtain ⟨i, rfl⟩ := normalForm_cover k hx.1
  rcases eliminate_check k i with hi | hi | hi
  · rw [hi, normalForm_central]
  · exact (hi ((normal_count_eq k i i).symm.trans hx.2.1)).elim
  · exact (hx.2.2 _ (normalForm_mem k (badIndex k i))
      ((normal_count_eq k i (badIndex k i)).trans hi)).elim

/-- A realizing permutation transports the common fixed-point set bijectively. -/
theorem commonFixedCount_automorphism
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (a : MulAut Held.He) (x y : Held.He) :
    commonFixedCount (a x) (a y) = commonFixedCount x y := by
  obtain ⟨g, rfl⟩ := hreal a
  symm
  apply Finset.card_bijective g.val g.val.bijective
  intro v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hx : Held.representation (Held.permutationGroup.normalizerMonoidHom g x) (g.val v) =
      g.val (Held.representation x v) := by
    change g.val (Held.representation x (g.val.symm (g.val v))) = _
    rw [Equiv.symm_apply_apply]
  have hy : Held.representation (Held.permutationGroup.normalizerMonoidHom g y) (g.val v) =
      g.val (Held.representation y v) := by
    change g.val (Held.representation y (g.val.symm (g.val v))) = _
    rw [Equiv.symm_apply_apply]
  rw [hx, hy]
  simp only [Equiv.apply_eq_iff_eq]

theorem signature_map
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (k : Fin 2) (a : MulAut Held.He)
    (ha : a ∈ automorphismNormalizer (heldRow (rowIndex k)))
    (x : Held.He) (hx : Signature k x) : Signature k (a x) := by
  change (heldRow (rowIndex k)).map a.toMonoidHom = heldRow (rowIndex k) at ha
  have hmem (y : Held.He) : a y ∈ heldRow (rowIndex k) ↔ y ∈ heldRow (rowIndex k) := by
    have hm := mem_map_iff_mem (f := a.toMonoidHom) a.injective
      (K := heldRow (rowIndex k)) (x := y)
    rwa [ha] at hm
  refine ⟨(hmem x).mpr hx.1, ?_, ?_⟩
  · rw [commonFixedCount_automorphism hreal]
    exact hx.2.1
  · intro y hy
    have hy' : a.symm y ∈ heldRow (rowIndex k) := (hmem _).mp (by simpa using hy)
    have hc := commonFixedCount_automorphism hreal a x (a.symm y)
    rw [a.apply_symm_apply] at hc
    rw [hc]
    exact hx.2.2 _ hy'

end Middle

/-- Every full normalizer of either middle row preserves the first row. -/
theorem ambientRow_middle_normalizer_le_zero
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (k : Fin 2) :
    normalizer (ambientRow (Middle.rowIndex k) : Set (MulAut Held.He)) ≤
      normalizer (ambientRow 0 : Set (MulAut Held.He)) := by
  rw [ambientRow_normalizer, ambientRow_normalizer]
  intro a ha
  have he : a rowZeroElement = rowZeroElement := Middle.signature_unique k _
    (Middle.signature_map hreal k a ha _ (Middle.central_signature k))
  change (heldRow 0).map a.toMonoidHom = heldRow 0
  rw [heldRow_zero_eq_zpowers, MonoidHom.map_zpowers]
  exact congrArg zpowers he

/-- The middle rows are placed in the same max5 conjugate as the first row. -/
theorem ambientRow_middle_normalizer_le
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (k : Fin 2) :
    normalizer (ambientRow (Middle.rowIndex k) : Set (MulAut Held.He)) ≤
      (candidate false).map (MulAut.conj (MulAut.conj rowZeroConjugator)).toMonoidHom :=
  (ambientRow_middle_normalizer_le_zero hreal k).trans ambientRow_zero_normalizer_le

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.NormalizerInclusions
