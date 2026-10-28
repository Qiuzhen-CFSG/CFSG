module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.Generation
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointGeometry
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneGeometry
public import Mathlib.Algebra.Group.Subgroup.Order

/-!+# Maximality and local geometry of the projective unitary-four amalgam

For every n ≥ 1, the two coordinate parabolics in PSU₄(2ⁿ) are maximal
proper subgroups and generate the whole projective group. Their whole
intersection is maximal inside each parabolic, including for n = 1.

The matrix theorems prove maximality by root operations and elimination in
the antidiagonal Hermitian model. We specialize those results to the stored
field and involution, and transport along the literal canonical projective
map. Its injectivity identifies the full flag stabilizers inside the two
parabolics; its surjectivity also transports ambient maximality. The final
`parabolic_geometry` theorem states the local conclusions for the ranges of
the actual amalgam embeddings.

Source: Aschbacher--Smith F.1.4--7, printed pp.260--261, and the U₄(q)
amalgam in F.1.12(I)(6), printed pp.263--264 of `refs/quasithin.pdf`.
This discharges generation and parabolic/flag maximality for the concrete
model. The full F.1.12 classification, local-factor descriptions, and
degree-two extension are separate results.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary

variable (n : ℕ) (hn : 1 ≤ n)

/-- Ambient maximality of the matrix point stabilizer. -/
theorem pointParabolicMatrix_isCoatom : IsCoatom (pointParabolicMatrix n hn) :=
  UnitaryFourPointGeometry.pointParabolic_isCoatom (MatrixField n)
    (fieldConj n) (fieldConj_involutive n hn)

/-- Ambient maximality of the matrix plane stabilizer. -/
theorem planeParabolicMatrix_isCoatom : IsCoatom (planeParabolicMatrix n hn) :=
  UnitaryFourPlaneGeometry.plane_isCoatom (MatrixField n)
    (fieldConj n) (fieldConj_involutive n hn)

/-- The whole matrix flag stabilizer is maximal in the whole point parabolic. -/
theorem overlapMatrix_isCoatom_in_point :
    IsCoatom ((overlapMatrix n hn).subgroupOf (pointParabolicMatrix n hn)) :=
  UnitaryFourPointGeometry.borel_subgroupOf_point_isCoatom (MatrixField n)
    (fieldConj n) (fieldConj_involutive n hn)

/-- The whole matrix flag stabilizer is maximal in the whole plane parabolic. -/
theorem overlapMatrix_isCoatom_in_plane :
    IsCoatom ((overlapMatrix n hn).subgroupOf (planeParabolicMatrix n hn)) :=
  UnitaryFourPlaneGeometry.borel_isCoatom_in_plane (MatrixField n)
    (fieldConj n) (fieldConj_involutive n hn)

private theorem isCoatom_projective_iff (H : Subgroup (MatrixGroup n hn)) :
    IsCoatom (H.map (projection n hn)) ↔ IsCoatom H := by
  let e : MatrixGroup n hn ≃* ProjectiveGroup n hn :=
    MulEquiv.ofBijective (projection n hn)
      ⟨projection_injective n hn,
        UnitaryFourFlag.project_surjective (MatrixField n) (standardForm n hn)⟩
  exact OrderIso.isCoatom_iff e.mapSubgroup H

private theorem isCoatom_subgroupOf_projective_iff
    (B P : Subgroup (MatrixGroup n hn)) :
    IsCoatom ((B.map (projection n hn)).subgroupOf (P.map (projection n hn))) ↔
      IsCoatom (B.subgroupOf P) := by
  let e := P.equivMapOfInjective (projection n hn) (projection_injective n hn)
  have he : ((B.map (projection n hn)).subgroupOf (P.map (projection n hn))).comap
      (e : P →* P.map (projection n hn)) = B.subgroupOf P := by
    ext x
    change projection n hn x.val ∈ B.map (projection n hn) ↔ x.val ∈ B
    exact Subgroup.mem_map_iff_mem (projection_injective n hn)
  rw [← Subgroup.isCoatom_comap e, he]

/-- The actual projective point parabolic is a maximal proper subgroup. -/
theorem pointParabolic_isCoatom : IsCoatom (pointParabolic n hn) :=
  (isCoatom_projective_iff n hn _).mpr (pointParabolicMatrix_isCoatom n hn)

/-- The actual projective plane parabolic is a maximal proper subgroup. -/
theorem planeParabolic_isCoatom : IsCoatom (planeParabolic n hn) :=
  (isCoatom_projective_iff n hn _).mpr (planeParabolicMatrix_isCoatom n hn)

/-- Maximality uses the full projective overlap inside the full point parabolic. -/
theorem overlap_isCoatom_in_point :
    IsCoatom ((overlap n hn).subgroupOf (pointParabolic n hn)) :=
  (isCoatom_subgroupOf_projective_iff n hn _ _).mpr
    (overlapMatrix_isCoatom_in_point n hn)

/-- Maximality uses the full projective overlap inside the full plane parabolic. -/
theorem overlap_isCoatom_in_plane :
    IsCoatom ((overlap n hn).subgroupOf (planeParabolic n hn)) :=
  (isCoatom_subgroupOf_projective_iff n hn _ _).mpr
    (overlapMatrix_isCoatom_in_plane n hn)

/-- The left amalgam map has the entire flag stabilizer as its image. -/
theorem amalgam_left_range :
    (amalgam n hn).left.range = (overlap n hn).subgroupOf (pointParabolic n hn) :=
  Subgroup.inclusion_range (Subgroup.map_mono inf_le_left)

/-- The right amalgam map has the entire flag stabilizer as its image. -/
theorem amalgam_right_range :
    (amalgam n hn).right.range = (overlap n hn).subgroupOf (planeParabolic n hn) :=
  Subgroup.inclusion_range (Subgroup.map_mono inf_le_right)

theorem amalgam_left_range_isCoatom : IsCoatom (amalgam n hn).left.range := by
  rw [amalgam_left_range]
  exact overlap_isCoatom_in_point n hn

theorem amalgam_right_range_isCoatom : IsCoatom (amalgam n hn).right.range := by
  rw [amalgam_right_range]
  exact overlap_isCoatom_in_plane n hn

/-- Generation, exact overlap, and ambient and local maximality for the
literal projective flag amalgam, with no additional structural premises. -/
theorem parabolic_geometry :
    pointParabolic n hn ⊔ planeParabolic n hn = ⊤ ∧
    pointParabolic n hn ⊓ planeParabolic n hn = overlap n hn ∧
    IsCoatom (pointParabolic n hn) ∧ IsCoatom (planeParabolic n hn) ∧
    IsCoatom (amalgam n hn).left.range ∧ IsCoatom (amalgam n hn).right.range :=
  ⟨parabolics_generate n hn, exact_overlap n hn,
    pointParabolic_isCoatom n hn, planeParabolic_isCoatom n hn,
    amalgam_left_range_isCoatom n hn, amalgam_right_range_isCoatom n hn⟩

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
