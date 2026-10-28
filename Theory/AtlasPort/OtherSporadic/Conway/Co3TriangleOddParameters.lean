/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleOddParameters.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleCodeCounts
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleOddParameters.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

abbrev Co3OddFlags (a : Omega) (k : ℕ) (v w : Bit) :=
  (c : GolayCoordinateWeight k a v) × {b : Omega // b ≠ a ∧ c.val.val b = w}

theorem golay_one_fiber_card (c : golay) :
    Nat.card {b : Omega // c.val b = 1} = hammingNorm c.val := by
  let e : {b : Omega // c.val b = 1} ≃ {b // b ∈ support c.val} :=
    Equiv.subtypeEquivRight (fun b => (golay_coordinate_support c b).symm)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]
  rfl

theorem golay_zero_fiber_card (c : golay) :
    Nat.card {b : Omega // c.val b = 0} = 24-hammingNorm c.val := by
  let e : {b : Omega // c.val b = 0} ≃ {b : Omega // c.val b ≠ 1} :=
    Equiv.subtypeEquivRight (fun b => by rcases bit_cases (c.val b) with h | h <;> simp [h])
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,golay_one_fiber_card]
  norm_num [Omega,HexIndex]

theorem coordinate_fiber_erase_card (c : golay) (a : Omega) (w : Bit) :
    Nat.card {b : Omega // b ≠ a ∧ c.val b = w} =
      Nat.card {b : Omega // c.val b = w} - (if c.val a = w then 1 else 0) := by
  let S := Finset.univ.filter (fun b => c.val b = w)
  let e : {b : Omega // b ≠ a ∧ c.val b = w} ≃ {b // b ∈ S.erase a} :=
    Equiv.subtypeEquivRight (fun b => by simp [S])
  let f : {b : Omega // c.val b = w} ≃ {b // b ∈ S} :=
    Equiv.subtypeEquivRight (fun b => by simp [S])
  rw [Nat.card_congr e,Nat.card_congr f,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,
    Fintype.card_coe,Fintype.card_coe]
  by_cases ha : c.val a = w
  · rw [Finset.card_erase_of_mem (by simp [S,ha])]; simp [ha]
  · rw [Finset.erase_eq_of_notMem (by simp [S,ha])]; simp [ha]

theorem co3_odd_octad_inside_flags_card (a : Omega) : Nat.card (Co3OddFlags a 8 1 1) = 1771 := by
  rw [Nat.card_sigma]
  have hf (c : GolayCoordinateWeight 8 a 1) :
      Nat.card {b : Omega // b ≠ a ∧ c.val.val b = 1} = 7 := by
    rw [coordinate_fiber_erase_card,golay_one_fiber_card,c.prop.1,c.prop.2]; norm_num
  simp_rw [hf]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card]
  rw [golay_octad_coordinate_one_card]
  norm_num

theorem co3_odd_octad_outside_flags_card (a : Omega) : Nat.card (Co3OddFlags a 8 0 0) = 7590 := by
  rw [Nat.card_sigma]
  have hf (c : GolayCoordinateWeight 8 a 0) :
      Nat.card {b : Omega // b ≠ a ∧ c.val.val b = 0} = 15 := by
    rw [coordinate_fiber_erase_card,golay_zero_fiber_card,c.prop.1,c.prop.2]; norm_num
  simp_rw [hf]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card]
  rw [golay_octad_coordinate_zero_card]
  norm_num

theorem co3_odd_dodecad_flags_card (a : Omega) : Nat.card (Co3OddFlags a 12 0 1) = 15456 := by
  rw [Nat.card_sigma]
  have hf (c : GolayCoordinateWeight 12 a 0) :
      Nat.card {b : Omega // b ≠ a ∧ c.val.val b = 1} = 12 := by
    rw [coordinate_fiber_erase_card,golay_one_fiber_card,c.prop.1,c.prop.2]; norm_num
  simp_rw [hf]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card]
  rw [golay_dodecad_coordinate_zero_card]
  norm_num

end Atlas.Conway
