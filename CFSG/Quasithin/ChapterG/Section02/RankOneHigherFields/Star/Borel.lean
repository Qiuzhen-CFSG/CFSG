module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Star.GeometryData
public import Theory.SpecificGroups.SL2.LineBorelResidual
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The line-Borel residual and root commutator in higher-field G.2.3

The literal star image of N_L(V₁) is the full setwise stabilizer of the
marked field line. That matrix Borel is two-perfect, and the actual finite
surjection from N_L(V₁) preserves the two-residual. Consequently the
embedded O²(N_L(V₁)), which defines L₁, has that same star image.

Under the explicit identification of the matrix U-image with the pointwise
line fixer, its commutator with this Borel is itself. The calculation is
transported through the supplied SL₂ model and the inclusion into LT/O₂(LT).
The only extra premise is `hroot`; the independent line-root geometry branch
constructs it, and the higher-field Star assembly must discharge it. The
containment and Frattini premises are the preceding G.2.2 conclusions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.3, printed pp.333–334 (PDF pp.344–345), especially U* = [U*, L₁*].
-/

public section

open Subgroup Matrix
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Hypothesis
open Setup
variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F] {n : ℕ} {g : G}
  (d : Hypothesis D F n g)
include d

private theorem field_card_ge_four : 4 ≤ Nat.card F := by
  rw [d.field_card]
  calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by have := d.exponent_gt_one; omega)

/-- The actual star image of the full point normalizer is two-perfect. -/
theorem star_pointNormalizer_isPPerfect : IsPPerfect 2 (D.star (D.L ⊓ D.G₁)) := by
  let : CharP F 2 := d.field_char_two
  let A := (D.star (D.L ⊓ D.G₁)).subgroupOf (D.star D.L)
  let e : D.star (D.L ⊓ D.G₁) ≃*
      MulAction.stabilizer SL(2,F) (d.point : Set (Fin 2 → F)) :=
    (subgroupOfEquivOfLe (binary_star_mono (D := D) (show D.L ⊓ D.G₁ ≤ D.L from inf_le_left))).symm.trans
      ((d.model.subgroupMap A).trans (MulEquiv.subgroupCongr d.pointNormalizer_model))
  exact (SpecialLinearGroup.lineStabilizer_isPPerfect d.point d.point_dimension
    d.field_card_ge_four).of_surjective e.symm.toMonoidHom e.symm.surjective

/-- Passing to the original star quotient identifies the embedded two-residual
L₁ with the full point-normalizer image. -/
theorem star_L₁_eq_pointNormalizer : D.star D.L₁ = D.star (D.L ⊓ D.G₁) := by
  let N := D.L ⊓ D.G₁
  have hN : N ≤ D.LT := inf_le_left.trans le_sup_left
  let f := D.binaryStarRestriction N hN
  have hp : IsPPerfect 2 f.range := by
    change IsPPerfect 2 (D.binaryStarRestriction N hN).range
    rw [binaryStarRestriction_range]
    exact d.star_pointNormalizer_isPPerfect
  have he : (pResidual 2 N).map f.rangeRestrict = ⊤ := by
    rw [map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective]
    exact (pResidual_eq_top_iff 2 f.range).mpr hp
  have hi := congrArg (fun A : Subgroup f.range => A.map f.range.subtype) he
  rw [Subgroup.map_map, ← MonoidHom.range_eq_map, range_subtype] at hi
  change (pResidual 2 N).map f = f.range at hi
  have hL₁ : D.L₁ ≤ N := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hres : D.L₁.subgroupOf N = pResidual 2 N := by
    change ((pResidual 2 N).map N.subtype).comap N.subtype = _
    exact comap_map_eq_self_of_injective N.subtype_injective _
  rw [← hres, binaryStarRestriction_map N D.L₁ hN hL₁,
    binaryStarRestriction_range] at hi
  exact hi

/-- The source commutator equality on the literal star images, conditional only
on the independent line-root identification and the preceding G.2.2 premises. -/
theorem star_U_commutator_L₁ (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hroot : d.matrixU = fixingSubgroup SL(2,F) (d.point : Set (Fin 2 → F))) :
    ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U := by
  let : CharP F 2 := d.field_char_two
  have hc : ⁅(D.star D.U).subgroupOf (D.star D.L),
      (D.star (D.L ⊓ D.G₁)).subgroupOf (D.star D.L)⁆ =
      (D.star D.U).subgroupOf (D.star D.L) := by
    apply Subgroup.map_injective (f := d.model.toMonoidHom) d.model.injective
    rw [map_commutator, d.pointNormalizer_model]
    change ⁅d.matrixU, MulAction.stabilizer SL(2,F) (d.point : Set (Fin 2 → F))⁆ = d.matrixU
    rw [hroot]
    exact SpecialLinearGroup.commutator_lineFixer_stabilizer d.point d.point_dimension
      d.field_card_ge_four
  have hi := congrArg (fun A : Subgroup (D.star D.L) => A.map (D.star D.L).subtype) hc
  rw [map_commutator, map_subgroupOf_eq_of_le (d.star_U_le_star_L hUT hf),
    map_subgroupOf_eq_of_le (binary_star_mono (D := D) (show D.L ⊓ D.G₁ ≤ D.L from inf_le_left))] at hi
  rw [d.star_L₁_eq_pointNormalizer]
  exact hi

end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Hypothesis
