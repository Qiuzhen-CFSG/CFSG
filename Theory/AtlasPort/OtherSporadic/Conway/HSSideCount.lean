/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSSideCount.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSSideParameters

/-!
The 11178 possible sides of the marked 2–3–3 Leech triangle.
A bijection with the five coordinate families reduces the count to Golay support counts.

Source: Gerald Höhn, `Atlas/Conway/HSSideCount.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def hsSideSize : Fin 5 → ℕ := ![23,506,5313,4048,1288]

theorem hs_pair_supports_card (a : Omega) : Nat.card (HSPairSupports a) = 23 := by
  change Nat.card {T // T ∈ ((Finset.univ : Finset Omega).powersetCard 2).filter
    (fun T => {a} ⊆ T)} = 23
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,
    Finset.card_filter_powersetCard_subset {a} Finset.univ 2 (Finset.subset_univ _) (by simp)]
  norm_num [Omega,HexIndex,Nat.choose]

theorem hs_side_parameters_card (a : Omega) (t : Fin 5) :
    Nat.card (HSSideParameters a t) = hsSideSize t := by
  fin_cases t
  · change Nat.card ((T : HSPairSupports a) × {s : T.val → Bit //
      s ⟨a,Finset.singleton_subset_iff.mp (Finset.mem_filter.mp T.prop).2⟩ = 0 ∧
      hammingNorm s = 1}) = 23
    rw [Nat.card_sigma]
    have hf (T : HSPairSupports a) : Nat.card {s : T.val → Bit //
        s ⟨a,Finset.singleton_subset_iff.mp (Finset.mem_filter.mp T.prop).2⟩ = 0 ∧
        hammingNorm s = 1} = 1 := by
      rw [binary_weight_zero_count,Fintype.card_coe,
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp T.prop).1).2]
      norm_num [Nat.choose]
    simp_rw [hf]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,← Nat.card_eq_fintype_card]
    exact hs_pair_supports_card a
  · change Nat.card (Co3OutsideOctads a) = 506
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,octads_avoiding_point_card]
  · change Nat.card ((T : Co3ThroughOctads a) × {s : T.val → Bit //
      s ⟨a,(Finset.mem_filter.mp T.prop).2⟩ = 0 ∧ hammingNorm s = 2}) = 5313
    rw [Nat.card_sigma]
    have hf (T : Co3ThroughOctads a) : Nat.card {s : T.val → Bit //
        s ⟨a,(Finset.mem_filter.mp T.prop).2⟩ = 0 ∧ hammingNorm s = 2} = 21 := by
      rw [binary_weight_zero_count,Fintype.card_coe,octad_size T.val (Finset.mem_filter.mp T.prop).1]
      norm_num [Nat.choose]
    simp_rw [hf]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe]
    rw [octads_through_point_card]; norm_num
  · change Nat.card (Co3OddFlags a 8 0 1) = 4048
    rw [Nat.card_sigma]
    have hf (c : GolayCoordinateWeight 8 a 0) :
        Nat.card {b : Omega // b ≠ a ∧ c.val.val b = 1} = 8 := by
      rw [coordinate_fiber_erase_card,golay_one_fiber_card,c.prop.1,c.prop.2]
      norm_num
    simp_rw [hf]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card]
    rw [golay_octad_coordinate_zero_card]; norm_num
  · change Nat.card (GolayCoordinateWeight 12 a 1) = 1288
    rw [golay_coordinate_one_card 12 dodecads dodecads_mem,dodecads_through_point_card]

instance hsSideParameters_finite (a : Omega) (t : Fin 5) : Finite (HSSideParameters a t) := by
  fin_cases t <;> infer_instance

def hsSideParameterMap (p : (t : Fin 5) × HSSideParameters co3MarkedCoordinate t) : HSSides :=
  ⟨hsSideParameterVector co3MarkedCoordinate p.1 p.2,
    hs_side_shape_sound _ _ _ (hs_side_parameter_shape _ _ p.2)⟩

theorem hsSideParameterMap_bijective : Function.Bijective hsSideParameterMap := by
  constructor
  · rintro ⟨s,p⟩ ⟨t,q⟩ h
    have he := congrArg Subtype.val h
    change hsSideParameterVector _ s p = hsSideParameterVector _ t q at he
    have hq := hs_side_parameter_shape co3MarkedCoordinate t q
    rw [← he] at hq
    have ht := hs_side_shape_unique _ s t _ (hs_side_parameter_shape _ s p) hq
    subst t
    have hp := hsSideParameterVector_injective _ s he
    subst q
    rfl
  · intro y
    obtain ⟨t,ht⟩ := hs_side_shape_exhaustive co3MarkedCoordinate y.val y.prop.1 y.prop.2
    obtain ⟨p,hp⟩ := hs_side_parameter_represents _ t y.val ht
    exact ⟨⟨t,p⟩,Subtype.ext hp⟩

def hsSideParameterEquiv : ((t : Fin 5) × HSSideParameters co3MarkedCoordinate t) ≃ HSSides :=
  Equiv.ofBijective hsSideParameterMap hsSideParameterMap_bijective

instance : Finite HSSides := Finite.of_equiv _ hsSideParameterEquiv

theorem hs_sides_card : Nat.card HSSides = 11178 := by
  rw [← Nat.card_congr hsSideParameterEquiv,Nat.card_sigma]
  simp_rw [hs_side_parameters_card]
  norm_num [Fin.sum_univ_succ,hsSideSize]

end Atlas.Conway
