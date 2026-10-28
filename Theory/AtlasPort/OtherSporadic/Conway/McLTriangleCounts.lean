/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLTriangleCounts.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLTriangleParameters

/-!
The McLaughlin triangle subcounts 1, 330, 462 and 1232.
Count octads and sign choices in the parameter bijection, giving 2025 triangles
and finite instances for each parameter family.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLTriangleCounts.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

private theorem binary_weight_one_count (α : Type*) [Fintype α] [DecidableEq α]
    (a : α) (k : ℕ) :
    Nat.card {s : α → Bit // hammingNorm s = k ∧ s a = 1} =
      (Fintype.card α).choose k - (Fintype.card α-1).choose k := by
  let e : {s : α → Bit // hammingNorm s = k ∧ s a = 1} ≃
      {s : {s : α → Bit // hammingNorm s = k} // ¬ s.val a = 0} := {
    toFun s := ⟨⟨s.val,s.prop.1⟩,by rw [s.prop.2]; decide⟩
    invFun s := ⟨s.val.val,s.val.prop,by
      rcases bit_cases (s.val.val a) with h | h
      · exact False.elim (s.prop h)
      · exact h⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  let f : {s : {s : α → Bit // hammingNorm s = k} // s.val a = 0} ≃
      {s : α → Bit // s a = 0 ∧ hammingNorm s = k} := {
    toFun s := ⟨s.val.val,s.prop,s.val.prop⟩
    invFun s := ⟨⟨s.val,s.prop.2⟩,s.prop.1⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,Nat.card_congr f,
    binary_weight_count_fintype,binary_weight_zero_count]

theorem mcl_octad_codes_zero_card : Nat.card (McLOctadCodes 0) = 330 := by
  let e : McLOctadCodes 0 ≃ {c : golay // hammingNorm c.val = 8 ∧
      co3MarkedCoordinate ∉ support c.val ∧ co3BasePoint.val ∉ support c.val} :=
    Equiv.subtypeEquivRight (fun c => by simp [support])
  rw [Nat.card_congr e,Nat.card_congr (golayWeightSupportEquiv 8 octads octads_mem
    (fun T => co3MarkedCoordinate ∉ T ∧ co3BasePoint.val ∉ T)),
    Nat.card_eq_fintype_card,Fintype.card_coe]
  convert octads_avoiding_pair_card _ _ (Ne.symm co3BasePoint.prop) using 1
  congr 1
  ext T
  simp only [Finset.mem_filter]

theorem mcl_octad_codes_one_card : Nat.card (McLOctadCodes 1) = 77 := by
  let e : McLOctadCodes 1 ≃ {c : golay // hammingNorm c.val = 8 ∧
      co3MarkedCoordinate ∈ support c.val ∧ co3BasePoint.val ∈ support c.val} :=
    Equiv.subtypeEquivRight (fun c => by simp [golay_coordinate_support])
  rw [Nat.card_congr e,Nat.card_congr (golayWeightSupportEquiv 8 octads octads_mem
    (fun T => co3MarkedCoordinate ∈ T ∧ co3BasePoint.val ∈ T)),
    Nat.card_eq_fintype_card,Fintype.card_coe]
  convert octads_through_pair_card _ _ (Ne.symm co3BasePoint.prop) using 1
  congr 1
  ext T
  simp only [Finset.mem_filter]

theorem mcl_mixed_octads_card : Nat.card McLMixedOctads = 176 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := octads.filter (fun T => co3BasePoint.val ∈ T))
    (p := fun T => co3MarkedCoordinate ∈ T)
  have he : (octads.filter (fun T => co3BasePoint.val ∈ T)).filter
      (fun T => co3MarkedCoordinate ∈ T) =
      octads.filter (fun T => co3MarkedCoordinate ∈ T ∧ co3BasePoint.val ∈ T) := by
    ext T; simp [and_left_comm,and_comm,and_assoc]
  have hf : (octads.filter (fun T => co3BasePoint.val ∈ T)).filter
      (fun T => ¬ co3MarkedCoordinate ∈ T) =
      octads.filter (fun T => co3MarkedCoordinate ∉ T ∧ co3BasePoint.val ∈ T) := by
    ext T; simp [and_left_comm,and_comm,and_assoc]
  rw [he,hf,octads_through_pair_card _ _ (Ne.symm co3BasePoint.prop),
    octads_through_point_card] at h
  change Nat.card {T // T ∈ octads.filter
    (fun T => co3MarkedCoordinate ∉ T ∧ co3BasePoint.val ∈ T)} = 176
  rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  omega

theorem mcl_octad_inside_fiber_card (c : McLOctadCodes 1) :
    Nat.card {b : Omega // b ≠ co3MarkedCoordinate ∧
      b ≠ co3BasePoint.val ∧ c.val.val b = 1} = 6 := by
  let S := (support c.val.val).erase co3MarkedCoordinate |>.erase co3BasePoint.val
  let e : {b : Omega // b ≠ co3MarkedCoordinate ∧
      b ≠ co3BasePoint.val ∧ c.val.val b = 1} ≃ {b // b ∈ S} :=
    Equiv.subtypeEquivRight (fun b => by
      simp [S,golay_coordinate_support,and_left_comm])
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]
  change ((support c.val.val).erase co3MarkedCoordinate |>.erase co3BasePoint.val).card = 6
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨co3BasePoint.prop,
    (golay_coordinate_support c.val _).mpr c.prop.2.2⟩),Finset.card_erase_of_mem
    ((golay_coordinate_support c.val _).mpr c.prop.2.1)]
  change hammingNorm c.val.val - 1 - 1 = 6
  rw [c.prop.1]

def mclTriangleSize : Fin 4 → ℕ := ![1,330,462,1232]

theorem mcl_triangle_parameters_card (t : Fin 4) :
    Nat.card (McLTriangleParameters t) = mclTriangleSize t := by
  fin_cases t
  · simp [McLTriangleParameters,mclTriangleSize]
  · exact mcl_octad_codes_zero_card
  · change Nat.card ((c : McLOctadCodes 1) × {b : Omega //
      b ≠ co3MarkedCoordinate ∧ b ≠ co3BasePoint.val ∧ c.val.val b = 1}) = 462
    rw [Nat.card_sigma]
    simp_rw [mcl_octad_inside_fiber_card]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card]
    rw [mcl_octad_codes_one_card]; norm_num
  · change Nat.card ((T : McLMixedOctads) × {s : T.val → Bit // hammingNorm s = 2 ∧
      s ⟨co3BasePoint.val,(Finset.mem_filter.mp T.prop).2.2⟩ = 1}) = 1232
    rw [Nat.card_sigma]
    have hf (T : McLMixedOctads) : Nat.card {s : T.val → Bit // hammingNorm s = 2 ∧
        s ⟨co3BasePoint.val,(Finset.mem_filter.mp T.prop).2.2⟩ = 1} = 7 := by
      rw [binary_weight_one_count,Fintype.card_coe,
        octad_size T.val (Finset.mem_filter.mp T.prop).1]
      norm_num [Nat.choose]
    simp_rw [hf]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card]
    rw [mcl_mixed_octads_card]; norm_num

instance mclTriangleParameters_finite (t : Fin 4) : Finite (McLTriangleParameters t) := by
  fin_cases t <;> infer_instance

instance : Finite McLTriangles := Finite.of_equiv _ mclTriangleParameterEquiv

theorem mcl_triangles_card : Nat.card McLTriangles = 2025 := by
  rw [← Nat.card_congr mclTriangleParameterEquiv,Nat.card_sigma]
  simp_rw [mcl_triangle_parameters_card]
  norm_num [Fin.sum_univ_succ,mclTriangleSize]

end Atlas.Conway
