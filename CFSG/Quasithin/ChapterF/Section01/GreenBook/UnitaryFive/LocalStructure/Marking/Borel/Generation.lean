module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Marking.Borel.Right
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Borel.LineEigenvalue

/-!
# Generation and multiplication of the residual flag intersections

A nonidentity cubic diagonal element of the plane SL₂ Levi lies in the
right residual and in the overlap. It cannot lie in the left residual:
its eigenvalue on the marked line is not a fifth root. The left residual
intersection has index three in the overlap, so these two intersections
generate it. Relative normality turns this join into their pointwise product.

Source: Aschbacher--Smith F.1.3(4) and F.1.12(7), printed pp.260 and 263--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Matrix BenderSuzuki.MatrixGroups Theory.SpecificGroups.UnitaryFive
open scoped Pointwise
variable (M : Model 4)

/-- A concrete cubic plane-Levi element distinguishes the two residual intersections. -/
theorem rightLocal_overlap_not_le_leftLocal :
    ¬ M.rightLocalImage ⊓ M.overlap ≤ M.leftLocalImage := by
  have : Nontrivial M.LineCubic := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [M.lineCubic_card]; decide)
  obtain ⟨b, hb⟩ := exists_ne (1 : M.LineCubic)
  let a : M.F := b.val
  have ha : a ≠ 0 := b.val.ne_zero
  have h3 : a ^ 3 = 1 := (mem_rootsOfUnity' 3 b.val).mp b.property
  have h5 : a ^ 5 ≠ 1 := by
    intro h
    have h6 : a ^ 6 = 1 := by rw [show 6 = 3 * 2 by decide, pow_mul, h3, one_pow]
    rw [show 6 = 5 + 1 by decide, pow_succ, h, one_mul] at h6
    exact hb (Subtype.ext (Units.ext h6))
  let A := SpecialLinearGroup.diag2 a ha
  let s := PlaneCore.planeLeviSU M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix
    (PlaneCore.planeSLtoGL A)
  let g : M.Carrier := (M.rightSLLevi A).val
  have hR : g ∈ M.rightLocalImage := by
    refine ⟨M.rightSLLevi A, ?_, rfl⟩
    rw [M.rightLocal_eq_rightRadicalLevi, M.rightRadicalLevi_eq]
    exact Subgroup.mem_sup_right ⟨A,rfl⟩
  have hB : g ∈ M.overlap := by
    constructor
    · exact (Flag.planeSL_mem_line_iff M.form M.rightLeviTrace
        M.rightLeviTrace_spec M.matrix A).mpr (by simp [A, SpecialLinearGroup.diag2_coe'])
    · exact (M.rightSLLevi A).property
  intro hle
  have hg := hle ⟨hR,hB⟩
  have hs : project M.form s ∈ (LineCore.Parabolic.radicalLeviSubgroup M.form M.matrix).map
      (lineParabolic M.form).subtype := by
    change g ∈ (M.lineRadicalLeviSubgroup.map M.leftParabolic.subtype)
    rw [← M.leftLocal_eq_lineRadicalLeviSubgroup]
    exact hg
  apply h5
  apply Flag.Borel.residual_line_eigenvalue_fifth M.form M.matrix M.conjugation s a _ hs
  have hh := PlaneCore.planeLeviGL_plane M.form M.rightLeviTrace (PlaneCore.planeSLtoGL A) ![1,0]
  change (PlaneCore.planeLeviGL M.form M.rightLeviTrace (PlaneCore.planeSLtoGL A)).val *ᵥ
    ![1,1,0,0,0] = a • ![1,1,0,0,0]
  change (PlaneCore.planeLeviGL M.form M.rightLeviTrace (PlaneCore.planeSLtoGL A)).val *ᵥ
    ![1,1,0,0,0] = _ at hh
  rw [hh]
  ext i
  fin_cases i <;> simp [planeEquiv, PlaneCore.planeSLtoGL, A, SpecialLinearGroup.diag2_coe']

/-- The left residual restricts to a normal subgroup of the overlap. -/
theorem leftLocalImage_normal_in_overlap :
    (M.leftLocalImage.subgroupOf M.overlap).Normal := by
  have : (M.leftLocalImage.comap M.leftParabolic.subtype).Normal :=
    M.leftLocalImage_normal_in_parabolic
  change (M.leftLocalImage.comap (M.leftParabolic.subtype.comp M.amalgam.left)).Normal
  rw [← Subgroup.comap_comap]
  infer_instance

/-- The right residual restricts to a normal subgroup of the overlap. -/
theorem rightLocalImage_normal_in_overlap :
    (M.rightLocalImage.subgroupOf M.overlap).Normal := by
  have : (M.rightLocalImage.comap M.rightParabolic.subtype).Normal :=
    M.rightLocalImage_normal_in_parabolic
  change (M.rightLocalImage.comap (M.rightParabolic.subtype.comp M.amalgam.right)).Normal
  rw [← Subgroup.comap_comap]
  infer_instance

/-- The left residual cuts out an index-three subgroup of the overlap. -/
theorem leftLocalImage_overlap_index : (M.leftLocalImage.subgroupOf M.overlap).index = 3 := by
  change M.leftLocalImage.relIndex M.overlap = 3
  rw [← Subgroup.map_subgroupOf_eq_of_le (show M.overlap ≤ M.leftParabolic from inf_le_left)]
  change (M.leftLocal.map M.leftParabolic.subtype).relIndex
    ((M.overlap.subgroupOf M.leftParabolic).map M.leftParabolic.subtype) = 3
  rw [Subgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective,
    ← Subgroup.relIndex_sup_left, M.leftLocal_sup_overlap,
    Subgroup.relIndex_top_right, M.leftLocal_index_eq_three]

/-- The two actual residual intersections generate the entire overlap. -/
theorem residual_intersections_sup :
    (M.leftLocalImage ⊓ M.overlap) ⊔ (M.rightLocalImage ⊓ M.overlap) = M.overlap := by
  let X := M.leftLocalImage.subgroupOf M.overlap
  let Y := M.rightLocalImage.subgroupOf M.overlap
  have hXY : ¬ Y ≤ X := by
    intro hle
    apply M.rightLocal_overlap_not_le_leftLocal
    intro g hg
    exact hle (show (⟨g,hg.2⟩ : M.overlap) ∈ Y from hg.1)
  have hlt : X < X ⊔ Y := lt_of_le_of_ne le_sup_left (by
    intro he
    exact hXY (he ▸ le_sup_right))
  have hidx : (X ⊔ Y).index = 1 := by
    have hd := Subgroup.index_dvd_of_le (show X ≤ X ⊔ Y from le_sup_left)
    have hb := Subgroup.index_strictAnti hlt
    have hx : X.index = 3 := M.leftLocalImage_overlap_index
    rw [hx] at hd hb
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
    · exact h
    · omega
  have hh := congrArg (Subgroup.map M.overlap.subtype) (Subgroup.index_eq_one.mp hidx)
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hh
  exact hh

/-- Relative normality realizes that generation as an actual pointwise product. -/
theorem residual_intersections_product :
    (M.overlap : Set M.Carrier) =
      (M.leftLocalImage ⊓ M.overlap : Set M.Carrier) *
        (M.rightLocalImage ⊓ M.overlap : Set M.Carrier) := by
  conv_lhs => rw [← M.residual_intersections_sup]
  apply Subgroup.coe_mul_of_right_le_normalizer_left
  apply le_trans inf_le_right
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (show M.leftLocalImage ⊓ M.overlap ≤
    M.overlap from inf_le_right)).mp
  rw [Subgroup.inf_subgroupOf_right]
  exact M.leftLocalImage_normal_in_overlap
end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
