/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleParameters.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleOddParameters
public import Theory.AtlasPort.OtherSporadic.Lattices.SupportSignWeights
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleParameters.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev Co3ThroughOctads (a : Omega) := {T // T ∈ octads.filter (fun T => a ∈ T)}
abbrev Co3OutsideOctads (a : Omega) := {T // T ∈ octads.filter (fun T => a ∉ T)}

abbrev Co3TriangleParameters (a : Omega) : Fin 8 → Type
  | 0 => PUnit
  | 1 => {T // T ∈ (Finset.univ.erase a).powersetCard 2}
  | 2 => GolayCoordinateWeight 16 a 1
  | 3 => Co3OddFlags a 8 1 1
  | 4 => Co3OddFlags a 8 0 0
  | 5 => (T : Co3ThroughOctads a) ×
      {s : T.val → Bit // s ⟨a,(Finset.mem_filter.mp T.prop).2⟩ = 0 ∧ hammingNorm s = 4}
  | 6 => (T : Co3OutsideOctads a) × {s : T.val → Bit // hammingNorm s = 2}
  | 7 => Co3OddFlags a 12 0 1

def co3TriangleSize : Fin 8 → ℕ := ![1,253,506,1771,7590,8855,14168,15456]

theorem co3_triangle_parameters_card (a : Omega) (t : Fin 8) :
    Nat.card (Co3TriangleParameters a t) = co3TriangleSize t := by
  fin_cases t
  · simp [Co3TriangleParameters,co3TriangleSize]
  · change Nat.card {T // T ∈ (Finset.univ.erase a).powersetCard 2} = 253
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,Finset.card_powersetCard,
      Finset.card_erase_of_mem (Finset.mem_univ a)]
    norm_num [Omega,HexIndex,Nat.choose]
  · exact golay_sixteen_coordinate_one_card a
  · exact co3_odd_octad_inside_flags_card a
  · exact co3_odd_octad_outside_flags_card a
  · change Nat.card ((T : Co3ThroughOctads a) ×
      {s : T.val → Bit // s ⟨a,(Finset.mem_filter.mp T.prop).2⟩ = 0 ∧ hammingNorm s = 4}) = 8855
    rw [Nat.card_sigma]
    have hf (T : Co3ThroughOctads a) : Nat.card
        {s : T.val → Bit // s ⟨a,(Finset.mem_filter.mp T.prop).2⟩ = 0 ∧ hammingNorm s = 4} = 35 := by
      rw [binary_weight_zero_count,Fintype.card_coe,octad_size T.val (Finset.mem_filter.mp T.prop).1]
      norm_num [Nat.choose]
    simp_rw [hf]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe]
    rw [octads_through_point_card]; norm_num
  · change Nat.card ((T : Co3OutsideOctads a) × {s : T.val → Bit // hammingNorm s = 2}) = 14168
    rw [Nat.card_sigma]
    have hf (T : Co3OutsideOctads a) : Nat.card {s : T.val → Bit // hammingNorm s = 2} = 28 := by
      rw [binary_weight_count_fintype,Fintype.card_coe,octad_size T.val (Finset.mem_filter.mp T.prop).1]
      norm_num [Nat.choose]
    simp_rw [hf]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe]
    rw [octads_avoiding_point_card]; norm_num
  · exact co3_odd_dodecad_flags_card a

instance co3TriangleParameters_finite (a : Omega) (t : Fin 8) : Finite (Co3TriangleParameters a t) := by
  fin_cases t <;> infer_instance

theorem co3_triangle_total_parameters_card (a : Omega) :
    Nat.card ((t : Fin 8) × Co3TriangleParameters a t) = 48600 := by
  rw [Nat.card_sigma]
  simp_rw [co3_triangle_parameters_card]
  norm_num [Fin.sum_univ_succ,co3TriangleSize]

end Atlas.Conway
