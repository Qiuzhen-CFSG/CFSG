module

public import Theory.SpecificGroups.Rudvalis.Model.LowCentralizers
public import Theory.SpecificGroups.Rudvalis.Model.SylowInvariantPair
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow

/-!
# Whole Sylow centers in the central Rudvalis involution class

The existing Sylow order and center upper bound give center order exactly
two. The marked local Sylow center is fused to b² by two checked conjugators.
Conjugating its Sylow and comparing subgroup orders proves that every b²-class
involution generates the entire ambient image of a Sylow center.

This discharges the Sylow-center step in the source-local component-fusion
argument. The still-needed identification of component involutions with this
class is not assumed here.
Source: Aschbacher–Smith, 16.3.4, printed p.1178; GLS3 Table 5.3r.
-/

@[expose] public section

open Subgroup
namespace Rudvalis.InvolutionCentralizers
open Theory.GroupTheory.DoubleCoverCentralizer
open SylowOvergroups.RadicalCoverage.LocalCover

/-- Every actual Rudvalis Sylow two-subgroup has order 2¹⁴. -/
theorem sylow_card (P : Sylow 2 Model) : Nat.card P = 16384 := by
  rw [Nat.card_congr (P.equiv SylowInvariantPair.sylow).toEquiv]
  exact IntrinsicSylow.localP_card

/-- Every actual Rudvalis Sylow two-subgroup has center of order two. -/
theorem sylow_center_card (P : Sylow 2 Model) : Nat.card (center P) = 2 := by
  let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by rw [sylow_card]; decide)
  let : Nontrivial (center P) := P.isPGroup'.center_nontrivial
  exact Nat.le_antisymm (SylowCenter.sylow_center_card_le_two P)
    (Finite.one_lt_card (α := center P))

private theorem twoCentral_of_isConj {s t : Model} (h : IsConj s t)
    (hs : TwoCentral s) : TwoCentral t := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have hgt : (MulAut.conj g) s = t := hg
  simpa only [hgt] using hs.map (MulAut.conj g)

/-- The marked b² involution is central in an actual ambient Sylow subgroup. -/
theorem square_twoCentral : TwoCentral (b ^ 2) := by
  have hmem : elementaryGenerator 0 ∈ elementary 0 :=
    subset_closure (Set.mem_singleton _)
  rw [SylowInvariantPair.elementary_zero_eq_center] at hmem
  obtain ⟨z, hz, he⟩ := mem_map.mp hmem
  have hbase : TwoCentral (elementaryGenerator 0) := by
    rw [← he]
    exact ⟨SylowInvariantPair.sylow, z.property, hz⟩
  have hlocal : IsConj Max6Certificate.centralInvolution (elementaryGenerator 0) :=
    isConj_iff.mpr ⟨Max6Certificate.conjugator, Max6Certificate.conjugator_alignment⟩
  have hsquare : IsConj Max6Certificate.centralInvolution (b ^ 2) :=
    isConj_iff.mpr ⟨LowCentralizers.squareConjugator,
      LowCentralizers.squareConjugator_alignment⟩
  exact twoCentral_of_isConj (hlocal.symm.trans hsquare) hbase

/-- A b²-class involution generates the whole center of an actual Sylow subgroup. -/
theorem exists_sylow_center_eq_of_isConj_square (v : Model) (hv : orderOf v = 2)
    (hclass : IsConj v (b ^ 2)) :
    ∃ P : Sylow 2 Model, (center P).map (P : Subgroup Model).subtype = zpowers v := by
  obtain ⟨P, hvP, hc⟩ := twoCentral_of_isConj hclass.symm square_twoCentral
  have hle : zpowers v ≤ (center P).map (P : Subgroup Model).subtype :=
    zpowers_le.mpr (mem_map.mpr ⟨⟨v, hvP⟩, hc, rfl⟩)
  refine ⟨P, (eq_of_le_of_card_ge hle ?_).symm⟩
  rw [card_map_of_injective (P : Subgroup Model).subtype_injective,
    sylow_center_card, Nat.card_zpowers, hv]

end Rudvalis.InvolutionCentralizers
