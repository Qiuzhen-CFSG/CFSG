module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Marking.Borel.Left
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Marking.Borel.Generation

/-!
# Borel geometry of the concrete unitary-five flag

The common Sylow is normal in the whole overlap, and its normalizers in both
full parabolics are the corresponding flag subgroups. The intrinsic residual
normalizer images B₁ and B₂ are precisely the residual intersections with
the overlap. They are normal relative to the overlap and generate it: a
cubic element of the plane Levi distinguishes the two index-three residual
characters, using the exact fifth-root projective kernel.

Relative normality makes the subgroup join an actual pointwise product.
Since the common Sylow T lies in both Borels, this proves the literal source
identity B = B₁ B₂ T. Every model theorem is unconditional.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.3(4) and F.1.12(7), printed pp.260 and 263--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open scoped Pointwise
variable (M : Model 4)

/-- B₁ is normal relative to the full overlap. -/
theorem leftSylowNormalizerImage_normal_in_overlap :
    (M.leftSylowNormalizerImage.subgroupOf M.overlap).Normal := by
  rw [M.leftSylowNormalizerImage_eq, Subgroup.inf_subgroupOf_right]
  exact M.leftLocalImage_normal_in_overlap

/-- B₂ is normal relative to the full overlap. -/
theorem rightSylowNormalizerImage_normal_in_overlap :
    (M.rightSylowNormalizerImage.subgroupOf M.overlap).Normal := by
  rw [M.rightSylowNormalizerImage_eq, Subgroup.inf_subgroupOf_right]
  exact M.rightLocalImage_normal_in_overlap

/-- The intrinsic residual normalizer images generate the full overlap. -/
theorem sylowNormalizerImages_sup :
    M.leftSylowNormalizerImage ⊔ M.rightSylowNormalizerImage = M.overlap := by
  rw [M.leftSylowNormalizerImage_eq, M.rightSylowNormalizerImage_eq]
  exact M.residual_intersections_sup

/-- The two source Borels and the common Sylow generate the full overlap. -/
theorem sylowNormalizerImages_sup_flagTwoSubgroup :
    M.leftSylowNormalizerImage ⊔ M.rightSylowNormalizerImage ⊔ M.flagTwoSubgroup =
      M.overlap := by
  rw [sup_assoc, sup_of_le_left M.flagTwoSubgroup_le_rightSylowNormalizerImage,
    M.sylowNormalizerImages_sup]

/-- The two source Borels have the overlap as their pointwise product. -/
theorem sylowNormalizerImages_product :
    (M.overlap : Set M.Carrier) =
      (M.leftSylowNormalizerImage : Set M.Carrier) * (M.rightSylowNormalizerImage : Set M.Carrier) := by
  rw [M.leftSylowNormalizerImage_eq, M.rightSylowNormalizerImage_eq]
  exact M.residual_intersections_product

/-- The two source Borels permute as subsets of the actual common carrier. -/
theorem sylowNormalizerImages_permute :
    (M.leftSylowNormalizerImage : Set M.Carrier) * (M.rightSylowNormalizerImage : Set M.Carrier) =
      (M.rightSylowNormalizerImage : Set M.Carrier) * (M.leftSylowNormalizerImage : Set M.Carrier) := by
  symm
  apply Subgroup.set_mul_normalizer_comm
  have hB : M.overlap ≤ Subgroup.normalizer (M.leftSylowNormalizerImage : Set M.Carrier) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (by rw [M.leftSylowNormalizerImage_eq]; exact inf_le_right)).mp
        M.leftSylowNormalizerImage_normal_in_overlap
  exact (show M.rightSylowNormalizerImage ≤ M.overlap by
    rw [M.rightSylowNormalizerImage_eq]; exact inf_le_right).trans hB

/-- The literal source convention B = B₁ B₂ T holds as a pointwise set product. -/
theorem overlap_eq_borel_product :
    (M.overlap : Set M.Carrier) =
      (M.leftSylowNormalizerImage : Set M.Carrier) *
        (M.rightSylowNormalizerImage : Set M.Carrier) * (M.flagTwoSubgroup : Set M.Carrier) := by
  have hBT : (M.overlap : Set M.Carrier) * (M.flagTwoSubgroup : Set M.Carrier) = M.overlap := by
    apply Set.Subset.antisymm
    · exact Subgroup.mul_subset Set.Subset.rfl M.flagTwoSubgroup_le_overlap
    · intro g hg
      exact Set.mem_mul.mpr ⟨g,hg,1,M.flagTwoSubgroup.one_mem,mul_one g⟩
  calc
    (M.overlap : Set M.Carrier) =
      (M.overlap : Set M.Carrier) * (M.flagTwoSubgroup : Set M.Carrier) := hBT.symm
    _ = _ := by rw [M.sylowNormalizerImages_product]
end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
