module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.CentralInvolutionBounds
public import Theory.SpecificGroups.Held.TwoLocalCandidates.SelfNormalizing
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
public import Mathlib.GroupTheory.IndexNormal

/-!
# The Held involution centralizer from the representative normalizer

The published row-zero conjugator sends the fourth power of the first max5
generator to the common involution. This identity is checked on the certified
four-point base of the actual degree-2058 carrier.

The existing finite certificates give at least 21504 elements in max5 and at
most 43008 in the ambient involution centralizer. Thus max5 has relative index
at most two. The fixed two-subgroup is self-normalizing by the independent
orbit and colored-graph certificates in `Calculations.InnerNormalizer`, so the
Frattini argument makes max5 self-normalizing as well. Index two would make max5
normal inside the centralizer, forcing equality. Conjugation then gives the
required ambient containment with the unchanged catalogue conjugator.

The final containment requires only that the fixed representative is a two-group.
The representative-normalizer equality is discharged without using this centralizer
identification, the catalogue assembly, or a candidate maximality assertion.

Sources: GLS3 Table 5.3p (the 2B centralizer); the literal ATLAS HeG1-p2058B0 and
HeG1-max5W1 words; Aschbacher–Smith, condition E, printed pp.3–4 and 481–482.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Subgroup LocalPairs.SylowGeometry.Calculations

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
/-- The exact published conjugator identifies the two literal involutions. -/
public theorem conjugator_zero_max5First_four :
    (MulAut.conj (conjugator 0)) (max5First ^ 4) = centralWord := by
  apply eq_of_four_point_images
  decide +kernel

/-- The faithful Held action embeds its involution centralizer in the already
bounded graph centralizer. No ambient group order is assumed. -/
public theorem max5_involution_centralizer_card_le :
    Nat.card (centralizer ({max5First ^ 4} : Set He)) ≤ 43008 := by
  let C := centralizer ({max5First ^ 4} : Set He)
  let D := NormalizerGraph.preservingGroup ⊓
    centralizer ({representation (max5First ^ 4)} : Set (Equiv.Perm (Fin 2058)))
  have hmap : C.map representation ≤ D := by
    apply le_inf
    · rintro _ ⟨g, _, rfl⟩
      exact Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup g.property
    · simpa only [Set.image_singleton] using
        map_centralizer_le_centralizer_image ({max5First ^ 4} : Set He) representation
  have hcard := Nat.card_le_card_of_injective (Subgroup.inclusion hmap)
    (Subgroup.inclusion_injective hmap)
  rw [card_map_of_injective representation_injective] at hcard
  exact hcard.trans CentralInvolutionBounds.graph_centralizer_card_le

private theorem eq_of_self_normalizing_of_card_le_twice
    {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hle : H ≤ K)
    (hn : normalizer (H : Set G) = H)
    (hcard : Nat.card K ≤ 2 * Nat.card H) : K = H := by
  let L := H.subgroupOf K
  have he : Nat.card L = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
  have hi : L.index ≤ 2 := by
    have hc := L.card_mul_index
    rw [he] at hc
    have hp : 0 < Nat.card H := Nat.card_pos
    nlinarith
  by_cases ht : L = ⊤
  · exact le_antisymm (subgroupOf_eq_top.mp ht) hle
  · have hi2 : L.index = 2 := by
      have := L.one_lt_index_of_ne_top ht
      omega
    have hnormal : (H.subgroupOf K).Normal := L.normal_of_index_eq_two hi2
    have hKN : K ≤ normalizer (H : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hle).mp hnormal
    rw [hn] at hKN
    exact le_antisymm hKN hle

/-- The remaining representative-normalizer certificate identifies the actual
centralizer of the max5 involution, using only the certified finite bounds. -/
public theorem max5_involution_centralizer_eq_of_representative_normalizer
    (hp : IsPGroup 2 representative)
    (hn : normalizer (representative : Set He) = representative) :
    centralizer ({max5First ^ 4} : Set He) = max5 := by
  apply eq_of_self_normalizing_of_card_le_twice max5 _
    CentralInvolutionBounds.max5_le_centralizer
  · exact normalizer_eq_of_representative hp hn 2
  · have hl := CentralInvolutionBounds.max5_card_lower_bound
    have hu := max5_involution_centralizer_card_le
    omega

/-- Conditional assembly of the requested ambient upper inclusion. The sole
extra premise is the independent representative-normalizer equality. -/
public theorem centralWord_centralizer_le_of_representative_normalizer
    (hp : IsPGroup 2 representative)
    (hn : normalizer (representative : Set He) = representative) :
    centralizer ({centralWord} : Set He) ≤
      (subgroup (candidate 0)).map (MulAut.conj (conjugator 0)).toMonoidHom := by
  let e := MulAut.conj (conjugator 0)
  have hz : e (max5First ^ 4) = centralWord := conjugator_zero_max5First_four
  intro g hg
  refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
  change e.symm g ∈ max5
  rw [← max5_involution_centralizer_eq_of_representative_normalizer hp hn]
  apply mem_centralizer_singleton_iff.mpr
  apply e.injective
  simp only [map_mul, e.apply_symm_apply, hz]
  exact mem_centralizer_singleton_iff.mp hg

/-- The actual max5 involution centralizer, with the independent normalizer
certificate discharged. Only the representative's two-group property remains. -/
public theorem max5_involution_centralizer_eq
    (hp : IsPGroup 2 representative) :
    centralizer ({max5First ^ 4} : Set He) = max5 :=
  max5_involution_centralizer_eq_of_representative_normalizer hp InnerNormalizer.normalizer_eq

/-- The ambient centralizer of the common Held involution lies in the exact
published row-zero conjugate of max5. No extra model premise is required. -/
public theorem centralWord_centralizer_le
    (hp : IsPGroup 2 representative) :
    centralizer ({centralWord} : Set He) ≤
      (subgroup (candidate 0)).map (MulAut.conj (conjugator 0)).toMonoidHom :=
  centralWord_centralizer_le_of_representative_normalizer hp InnerNormalizer.normalizer_eq

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue
