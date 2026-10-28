module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Marking.Basic
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Marking.Borel
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Marking.Center

/-!
# Common Sylow markings for the U₅(4) amalgam

The concrete flag unipotent subgroup has order 2²⁰ and index 45 in the full
line--plane overlap. It is contained in both local residuals and is Sylow in
the residuals, parabolics and overlap, with compatible original amalgam maps.
Its relative normality identifies it with the overlap's canonical two-core.
The intrinsic local Sylow normalizers are the residual intersections with
the overlap and give the literal pointwise product B = B₁ B₂ T. Relative
normality of each residual turns parabolic generation into Pᵢ = Lᵢ B.
The line residual centralizes Z(T), fixing the source's left-side label.

The final theorem assembles these facts for the original full-overlap amalgam
and its literal inclusion maps, using only the field and form data in Model 4.
The local quotient and special-core results are re-exported through Basic;
the overall F.1.12(7) local-structure assembly remains in LocalStructure.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.3 and F.1.11--12(7), printed pp.260 and 262--264.
-/

public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model

open scoped Pointwise

variable (M : Model 4)

/-- Normality is relative to the full overlap, for the actual carrier subgroup. -/
theorem flagTwoSubgroup_normal_in_overlap :
    (M.flagTwoSubgroup.subgroupOf M.overlap).Normal :=
  M.overlapSylow_normal

/-- The common normal Sylow is the canonical two-core of the overlap. -/
theorem overlap_pCore_eq_sylow :
    pCore 2 M.overlap = (M.overlapSylow : Subgroup M.overlap) := by
  apply le_antisymm
  · exact pCore_isPGroup.le_sylow_of_normal M.overlapSylow
  · exact le_sSup ⟨M.overlapSylow_normal, M.overlapSylow.isPGroup'⟩

/-- In the common carrier, O₂(B) is exactly the constructed flag subgroup. -/
theorem overlap_pCore_map :
    (pCore 2 M.overlap).map M.overlap.subtype = M.flagTwoSubgroup := by
  rw [M.overlap_pCore_eq_sylow, M.overlapSylow_map]

/-- The literal source product L₁ B is the full line parabolic. -/
theorem leftParabolic_eq_local_mul_overlap :
    (M.leftParabolic : Set M.Carrier) =
      (M.leftLocalImage : Set M.Carrier) * (M.overlap : Set M.Carrier) := by
  rw [← M.leftLocalImage_sup_overlap]
  apply Subgroup.coe_mul_of_right_le_normalizer_left
  apply le_trans (show M.overlap ≤ M.leftParabolic from inf_le_left)
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (show M.leftLocalImage ≤ M.leftParabolic from
      (Subgroup.map_le_range _ _).trans_eq (Subgroup.range_subtype _))).mp
  exact M.leftLocalImage_normal_in_parabolic

/-- The literal source product L₂ B is the full plane parabolic. -/
theorem rightParabolic_eq_local_mul_overlap :
    (M.rightParabolic : Set M.Carrier) =
      (M.rightLocalImage : Set M.Carrier) * (M.overlap : Set M.Carrier) := by
  rw [← M.rightLocalImage_sup_overlap]
  apply Subgroup.coe_mul_of_right_le_normalizer_left
  apply le_trans (show M.overlap ≤ M.rightParabolic from inf_le_right)
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (show M.rightLocalImage ≤ M.rightParabolic from
      (Subgroup.map_le_range _ _).trans_eq (Subgroup.range_subtype _))).mp
  exact M.rightLocalImage_normal_in_parabolic

/-- The common Sylow, Borel products and centralizing label for the actual
U₅(4) amalgam. All Sylow and residual maps are the original subtype inclusions;
there is no additional local-structure or marking hypothesis. -/
theorem source_flag_marking :
    (M.flagTwoSubgroup.subgroupOf M.overlap).Normal ∧
    Nat.card M.flagTwoSubgroup = 2 ^ 20 ∧
    M.flagTwoSubgroup.relIndex M.overlap = 45 ∧
    M.flagTwoSubgroup ≤ M.leftLocalImage ⊓ M.rightLocalImage ∧
    (M.overlapSylow : Subgroup M.overlap).map M.overlap.subtype = M.flagTwoSubgroup ∧
    (M.overlapSylow : Subgroup M.overlap).map M.amalgam.left =
      (M.leftParabolicSylow : Subgroup M.leftParabolic) ∧
    (M.overlapSylow : Subgroup M.overlap).map M.amalgam.right =
      (M.rightParabolicSylow : Subgroup M.rightParabolic) ∧
    (M.leftLocalSylow : Subgroup M.leftLocal).map
      (M.leftParabolic.subtype.comp M.leftLocal.subtype) = M.flagTwoSubgroup ∧
    (M.rightLocalSylow : Subgroup M.rightLocal).map
      (M.rightParabolic.subtype.comp M.rightLocal.subtype) = M.flagTwoSubgroup ∧
    M.leftSylowNormalizerImage = M.leftLocalImage ⊓ M.overlap ∧
    M.rightSylowNormalizerImage = M.rightLocalImage ⊓ M.overlap ∧
    (M.leftParabolic : Set M.Carrier) =
      (M.leftLocalImage : Set M.Carrier) * (M.overlap : Set M.Carrier) ∧
    (M.rightParabolic : Set M.Carrier) =
      (M.rightLocalImage : Set M.Carrier) * (M.overlap : Set M.Carrier) ∧
    (M.overlap : Set M.Carrier) =
      (M.leftSylowNormalizerImage : Set M.Carrier) *
        (M.rightSylowNormalizerImage : Set M.Carrier) * (M.flagTwoSubgroup : Set M.Carrier) ∧
    M.leftLocalImage ≤ Subgroup.centralizer (M.flagCenter : Set M.Carrier) := by
  exact ⟨M.flagTwoSubgroup_normal_in_overlap, M.flagTwoSubgroup_card,
    M.flagTwoSubgroup_relIndex_overlap,
    le_inf M.flagTwoSubgroup_le_leftLocalImage M.flagTwoSubgroup_le_rightLocalImage,
    M.overlapSylow_map, M.amalgam_left_sylow_marking, M.amalgam_right_sylow_marking,
    M.leftLocalSylow_carrier_map, M.rightLocalSylow_carrier_map,
    M.leftSylowNormalizerImage_eq, M.rightSylowNormalizerImage_eq,
    M.leftParabolic_eq_local_mul_overlap, M.rightParabolic_eq_local_mul_overlap,
    M.overlap_eq_borel_product, M.leftLocalImage_le_centralizer_flagCenter⟩

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
