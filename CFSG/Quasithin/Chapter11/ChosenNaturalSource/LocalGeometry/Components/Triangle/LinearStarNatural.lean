module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearChiefCover
public import Theory.SpecificGroups.PSL3.LinearThreeRadicalCoordinates

/-!
# The marked natural action on the original star image

The original G.2.5 point-radical image, conjugated by the existing flag
alignment, is the concrete point radical in SL₃. Its affine coordinates
identify it with the natural plane for the SAME lower-right SL₂ block
used on V/V₁ and on the dual annihilator. The conjugation equation keeps
the full original star quotient, including its scalar center.

Injectivity follows from the original full SL₃ marking, and the already
proved star-image order gives surjectivity. No natural/dual layer is
assumed to have positive multiplicity. LinearChiefNatural applies these
coordinates to both projections of the selected chief section.
Source: Aschbacher--Smith 11.1.2, printed pp.763--764, using G.2.5.
-/

open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
open SL3 SL3.PlaneAction ChapterG.Section02.LinearThree Matrix.PSL3.LinearThree

/-- The full original star marking in the already chosen flag basis. -/
def pointAlignedStarModel :
    (linearPointSetup D S m (flag D S m)).star L ≃* SL(3,S.field.Carrier) :=
  (linearPointStarModel D S m (flag D S m)).trans (MulAut.conj (alignment D S m)⁻¹)

theorem pointAlignedStarModel_projection (l : L) :
    pointAlignedStarModel D S m
      (starProjection (linearPointSetup D S m (flag D S m)) l) = alignedQuotient D S m l := by
  change MulAut.conj (alignment D S m)⁻¹ (linearPointStarModel D S m _ _) = _
  rw [linearPointStarModel_projection]
  rfl

private theorem standard_radical_le_map {F : Type*} [Field F] :
    Matrix.PSL3.PointRadicalGeneration.radical
      (Matrix.PSL3.PointRadicalGeneration.standardPoint (F := F)) ≤
        (pointRadicalSL F).map (pointLocalSL F).subtype := by
  intro u hu
  rw [Matrix.PSL3.PointRadicalGeneration.radical_standardPoint,
    Matrix.PSL3.RootPlaneGeometry.mem_rootPlaneSL_point] at hu
  obtain ⟨a,b,rfl⟩ := hu
  let u := Matrix.PSL3Even.UnipotentGeometry.specialLinear F ⟨a,0,b⟩
  have hu : u ∈ pointLocalSL F := (mem_pointLocalSL_iff F u).mpr ⟨rfl,rfl,rfl⟩
  exact ⟨⟨u,hu⟩,(mem_pointRadicalSL_iff F ⟨u,hu⟩).mpr ⟨rfl,rfl,rfl,rfl⟩,rfl⟩

private theorem aligned_point_standard :
    Matrix.PSL3.PointRadicalGeneration.conjugatePoint ((flag D S m).space 0)
      (alignment D S m) = Matrix.PSL3.PointRadicalGeneration.standardPoint := by
  ext v
  rw [Matrix.PSL3.PointRadicalGeneration.mem_conjugatePoint]
  change specialLinearNatural 3 (alignment D S m) v ∈ Model.flagFor (alignment D S m) 0 ↔ _
  rw [mem_flagFor_iff]
  simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  exact (Matrix.PSL3.PointRadicalGeneration.mem_standardPoint v).symm

/-- The original star image is the natural plane for the same SL₂ marking
as V/V₁ and the dual annihilator. The source frame supplies the image;
no positivity of either upper-layer multiplicity is required. -/
theorem linear_point_star_natural_coordinates
    {g h : G}
    (d : Hypothesis (linearPointSetup D S m (flag D S m))
      S.field.Carrier S.field.degree g h)
    (hmodel : d.model = linearPointStarModel D S m (flag D S m))
    (hpoint : d.point = (flag D S m).space 0)
    (hUT : (linearPointSetup D S m (flag D S m)).U ≤ (T : Subgroup G))
    (hf : (frattini (linearPointSetup D S m (flag D S m)).U).map
      (linearPointSetup D S m (flag D S m)).U.subtype ≤ (flag D S m).Vi 0) :
    let B := linearPointSetup D S m (flag D S m)
    ∃ e : B.star B.U ≃* Multiplicative (Fin 2 → S.field.Carrier),
      ∀ (l : (flag D S m).Li 0) (u v : B.star B.U),
        (v : B.Star) = (starProjection B ⟨l,(localResidual_le _ l.property).1⟩ : B.Star) *
          (u : B.Star) * (starProjection B ⟨l,(localResidual_le _ l.property).1⟩ : B.Star)⁻¹ →
        e v = Matrix.SL2.naturalAction S.field.Carrier (pointConstituentProjection D S m l) (e u) := by
  intro B
  let F := S.field.Carrier
  let R := (pointRadicalSL F).map (pointLocalSL F).subtype
  have hUL := d.star_U_le_star_L hUT hf
  let p := (pointAlignedStarModel D S m).toMonoidHom.comp (inclusion hUL)
  have hp : ∀ u, p u ∈ R := by
    intro u
    have hr := d.pointRadicalImage_le_radical hUT hf
      (show d.model ⟨u,hUL u.property⟩ ∈ d.pointRadicalImage from
        mem_map_of_mem d.model.toMonoidHom u.property)
    rw [hpoint,hmodel] at hr
    have hh := mem_map_of_mem (MulAut.conj (alignment D S m)⁻¹).toMonoidHom hr
    rw [Matrix.PSL3.PointRadicalGeneration.radical_conjugate,aligned_point_standard] at hh
    exact standard_radical_le_map hh
  let j := ((pointRadicalSL F).equivMapOfInjective (pointLocalSL F).subtype
    (pointLocalSL F).subtype_injective).symm
  let c := (pointRadicalCoordinates F).toMonoidHom.comp (j.toMonoidHom.comp (p.codRestrict R hp))
  have hc : Function.Injective c := (pointRadicalCoordinates F).injective.comp
    (j.injective.comp (by
      intro x y he
      exact inclusion_injective hUL ((pointAlignedStarModel D S m).injective
        (congrArg Subtype.val he))))
  have hcard : Nat.card (B.star B.U) = Nat.card (Multiplicative (Fin 2 → F)) := by
    rw [d.card_star_U hUT hf]
    simp only [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → F) ≃ (Fin 2 → F)),
      Nat.card_fun,Nat.card_fin]
    change 2 ^ (2 * S.field.degree) = Nat.card S.field.Carrier ^ 2
    rw [S.field.card_eq,←pow_mul,Nat.mul_comm]
  let e := MulEquiv.ofBijective c ((Nat.bijective_iff_injective_and_card c).mpr ⟨hc,hcard⟩)
  refine ⟨e,?_⟩
  intro l u v hv
  apply pointRadicalCoordinates_conjugate F (localProjection D S m 0 l)
    (j (p.codRestrict R hp u)) (j (p.codRestrict R hp v))
  apply Subtype.ext
  have hj (w : R) : ((j w : pointLocalSL F) : SL(3,F)) = w.val := by
    have hh := ((pointRadicalSL F).equivMapOfInjective (pointLocalSL F).subtype
      (pointLocalSL F).subtype_injective).apply_symm_apply w
    exact congrArg Subtype.val hh
  change ((j (p.codRestrict R hp v) : pointLocalSL F) : SL(3,F)) =
    (localProjection D S m 0 l).val *
      ((j (p.codRestrict R hp u) : pointLocalSL F) : SL(3,F)) *
        (localProjection D S m 0 l).val⁻¹
  rw [hj,hj,localProjection_coe,←pointAlignedStarModel_projection]
  change pointAlignedStarModel D S m (inclusion hUL v) =
    pointAlignedStarModel D S m _ * pointAlignedStarModel D S m (inclusion hUL u) *
      (pointAlignedStarModel D S m _)⁻¹
  rw [←map_inv,←map_mul,←map_mul]
  congr 1
  exact Subtype.ext hv

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
