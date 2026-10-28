module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.CubicCommutators.Data

/-!
# The marked order-nine subgroup of the actual Held normalizer

The map is literal conjugation by `localWord false ^ 3` on the previously
certified order-nine plane. The finite normalization identities put its image
inside the full normalizer of `representativeLargeSeed`. Plane coordinates
exhaust its nonidentity elements, so the eight action certificates apply to all
of them. No comparison with a different local normalizer is assumed.

Source: GLS3 Table 5.3p; Aschbacher--Smith, printed p.526.
-/

public section
namespace Held.AutomorphismLocalPair.CubicCommutators
open Subgroup LocalPairs.PairCoverage.LocalActions
open LocalPairs.PairCoverage.LocalActions.RepresentativeImages

attribute [local irreducible] gen conjugator

/-- The existing order-nine plane, in its required marking. -/
@[expose] def nineSubgroup : Subgroup He :=
  (candidateOdd false 0).map (MulAut.conj conjugator).toMonoidHom

theorem nineSubgroup_le : nineSubgroup ≤ representativeLargeLocal := by
  apply map_le_iff_le_comap.mpr
  apply (closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  change (MulAut.conj conjugator) (oddGenerator false 0 k) ∈ representativeLargeLocal
  simpa only [gen] using gen_mem_normalizer k

theorem nineSubgroup_card : Nat.card nineSubgroup = 9 := by
  rw [nineSubgroup, card_map_of_injective (MulAut.conj conjugator).injective,
    candidateOdd_card]

private theorem coordinates_cover : ∀ u v : Fin 3, u ≠ 0 ∨ v ≠ 0 →
    ∃ k : Fin 8, first k = u ∧ second k = v := by
  decide +kernel

private theorem exists_element_of_mem {x : He} (hx : x ∈ nineSubgroup) (hne : x ≠ 1) :
    ∃ k : Fin 8, x = element k := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← oddEmbedding_range false 0] at hy
  obtain ⟨v, rfl⟩ := hy
  have he : (MulAut.conj conjugator) (oddEmbedding false 0 v) =
      gen 0 ^ (v.toAdd 0).val * gen 1 ^ (v.toAdd 1).val := by
    rw [oddEmbedding_apply, map_mul, map_pow, map_pow]
    simp only [gen]
  have hcoords : (v.toAdd 0 : Fin 3) ≠ 0 ∨ (v.toAdd 1 : Fin 3) ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply hne
    change (MulAut.conj conjugator) (oddEmbedding false 0 v) = 1
    rw [he]
    simp only [h.1, h.2, ZMod.val_zero, pow_zero, one_mul]
  obtain ⟨k, hk0, hk1⟩ := coordinates_cover (v.toAdd 0) (v.toAdd 1) hcoords
  refine ⟨k, ?_⟩
  change (MulAut.conj conjugator) (oddEmbedding false 0 v) = element k
  rw [he, element, hk0, hk1]
  rfl

theorem nineSubgroup_commutator_bound {x : He} (hx : x ∈ nineSubgroup) (hne : x ≠ 1) :
    12 < Nat.card (⁅representativeLargeSeed, zpowers x⁆ : Subgroup He) := by
  obtain ⟨k, rfl⟩ := exists_element_of_mem hx hne
  exact element_commutator_bound k

end Held.AutomorphismLocalPair.CubicCommutators
