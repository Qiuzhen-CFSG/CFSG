module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.Seeds
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.FiniteCover
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions

/-!
# Assembly from local parabolic geometry and single-element extensions

The stored words specify thirty-eight literal conjugate parabolics, grouped
into eighteen trees for the 122 seeds. The independent geometry and extension
modules certify their local intersections/products and the divisibility
obstruction for adjoining an element outside the seed's listed parabolics.

The latter forces every element of K into their union: subgroup orders divide
the order of K, while the index of K divides the index of a subgroup of K.
The finite tree argument then places the entire K in one member. Inverse
conjugation gives exactly the requested marked-parabolic output. The final
`seed_overgroup_placement` supplies every certificate to the preserved
conditional reduction. No exhaustive seed catalogue or ATLAS maximal-subgroup
catalogue is used.

Source: Parrott (1972), section 5, p.683; the primary ATLAS Tits entry and
`SeedOvergroups/source/README.md` document the concrete candidate discovery.
-/

namespace Tits.MinimumIndex.LargeTwoOvergroups
open Subgroup ExceptionalParabolics SeedOvergroups

private theorem map_conj_inv (H : Subgroup Atlas1600Group) (g : Atlas1600Group) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Atlas1600Group := by
    ext x
    change g⁻¹ * (g * x * g⁻¹) * g = x
    group
  rw [he, Subgroup.map_id]

/-- Containment in a stored place gives the actual inverse conjugator. -/
public theorem placement_of_le_place (K : Subgroup Atlas1600Group) (j : Fin 38)
    (hK : K ≤ place j) :
    ∃ g : Atlas1600Group,
      K.map (MulAut.conj g).toMonoidHom ≤ first ∨
      K.map (MulAut.conj g).toMonoidHom ≤ second := by
  refine ⟨(placeConjugator j)⁻¹, ?_⟩
  have hm := Subgroup.map_mono
    (f := (MulAut.conj (placeConjugator j)⁻¹).toMonoidHom) hK
  rw [place, map_conj_inv] at hm
  unfold placeBase at hm
  split_ifs at hm with hj
  · exact Or.inl hm
  · exact Or.inr hm

/-- The single extension is a subgroup of the same literal K. -/
public theorem singleExtension_le {i : Fin 122} {K : Subgroup Atlas1600Group}
    (hseed : seed i ≤ K) {x : Atlas1600Group} (hx : x ∈ K) :
    singleExtension i x ≤ K := by
  apply sup_le hseed
  exact (closure_le _).mpr (by rintro y (rfl : y = x); exact hx)

/-- Divisibility of a forbidden single extension forces elementwise coverage. -/
public theorem seed_union_cover_of_extension_obstructions
    (houtside : ∀ (i : Fin 122) (x : Atlas1600Group),
      (∀ j ∈ placeIds i, x ∉ place j) →
      ¬ 2 ∣ (singleExtension i x).index ∨
      25 ∣ Nat.card (singleExtension i x) ∨ 13 ∣ Nat.card (singleExtension i x))
    (i : Fin 122) (K : Subgroup Atlas1600Group) (hseed : seed i ≤ K)
    (heven : 2 ∣ K.index) (h25 : ¬ 25 ∣ Nat.card K) (h13 : ¬ 13 ∣ Nat.card K) :
    ∀ x ∈ K, ∃ P ∈ places i, x ∈ P := by
  classical
  intro x hx
  by_contra hn
  have hout : ∀ j ∈ placeIds i, x ∉ place j := by
    intro j hj hxj
    exact hn ⟨place j, List.mem_map.mpr ⟨j, hj, rfl⟩, hxj⟩
  have hd : Nat.card (singleExtension i x) ∣ Nat.card K :=
    Subgroup.card_dvd_of_le (singleExtension_le hseed hx)
  rcases houtside i x hout with h | h | h
  · exact h (heven.trans (Subgroup.index_dvd_of_le (singleExtension_le hseed hx)))
  · exact h25 (h.trans hd)
  · exact h13 (h.trans hd)

/-- Exact conjugate placement, conditional on the two independent finite
certificate families. Even index excludes extensions with odd index; the
final assembly must still discharge every certificate premise. -/
public theorem seed_overgroup_placement_of_place_certificates
    (htree : ∀ t : Fin 18, LeafIntersections ((placePattern t).map place))
    (hproduct : ∀ t : Fin 18, ProductCompatible ((placePattern t).map place))
    (houtside : ∀ (i : Fin 122) (x : Atlas1600Group),
      (∀ j ∈ placeIds i, x ∉ place j) →
      ¬ 2 ∣ (singleExtension i x).index ∨
      25 ∣ Nat.card (singleExtension i x) ∨ 13 ∣ Nat.card (singleExtension i x))
    (i : Fin 122) (K : Subgroup Atlas1600Group) (hseed : seed i ≤ K)
    (heven : 2 ∣ K.index) (h25 : ¬ 25 ∣ Nat.card K) (h13 : ¬ 13 ∣ Nat.card K) :
    ∃ g : Atlas1600Group,
      K.map (MulAut.conj g).toMonoidHom ≤ first ∨
      K.map (MulAut.conj g).toMonoidHom ≤ second := by
  obtain ⟨P, hP, hKP⟩ := le_of_union (htree (seedPattern i)) (hproduct (seedPattern i)) K
    (seed_union_cover_of_extension_obstructions houtside i K hseed heven h25 h13)
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hP
  exact placement_of_le_place K j hKP

/-- Every proper overgroup of a concrete seed with even index and order
divisible by neither 25 nor 13 is conjugate into one of the two marked
parabolics. All geometry and extension certificates are discharged. -/
public theorem seed_overgroup_placement
    (i : Fin 122) (K : Subgroup Atlas1600Group) (hseed : seed i ≤ K)
    (_hK : K ≠ ⊤) (heven : 2 ∣ K.index)
    (h25 : ¬ 25 ∣ Nat.card K) (h13 : ¬ 13 ∣ Nat.card K) :
    ∃ g : Atlas1600Group,
      K.map (MulAut.conj g).toMonoidHom ≤ first ∨
      K.map (MulAut.conj g).toMonoidHom ≤ second :=
  seed_overgroup_placement_of_place_certificates
    placePattern_leafIntersections placePattern_productCompatible
    singleExtension_obstruction i K hseed heven h25 h13

end Tits.MinimumIndex.LargeTwoOvergroups
