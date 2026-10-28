module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ExtensionDiagram
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Marked

/-!
# Residual markings of restored original parabolics

The reduced and original endpoints have the same embedded solvable residual.
Consequently an original endpoint map extending the reduced marking takes its
residual to the inner image of the native residual. Combining this with the
whole-Borel restoration constructs the literal marking used by the original
extension consumers, without assuming perfectness of either selected factor.

Source: DGS, *Groups and Graphs* (1985), (15.2), pp.226–228, and the
normalized-Borel application in Aschbacher–Smith F.1.12, pp.263–264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open Chapter6.Source.RankOneGeneric

theorem reduced_residual_map_inclusion
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (i : Fin 2) :
    (solvableResidual (parabolic L (SuzukiContainment.reducedSylow L S) i)).map
      (inclusion (SuzukiContainment.reduced_parabolic_le h i)) =
        solvableResidual (parabolic L S i) := by
  apply map_injective (parabolic L S i).subtype_injective
  rw [map_map]
  exact SuzukiContainment.reduced_parabolic_residual h i

private theorem residual_image_of_restriction
    {G X : Type*} [Group G] [Group X]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (i : Fin 2) (Q : Subgroup X)
    (f : parabolic L S i →* MulAut X)
    (e : parabolic L (SuzukiContainment.reducedSylow L S) i ≃* Q)
    (he : ∀ x, f (inclusion (SuzukiContainment.reduced_parabolic_le h i) x) =
      MulAut.conj (e x).val) :
    (solvableResidual (parabolic L S i)).map f =
      ((solvableResidual Q).map Q.subtype).map MulAut.conj := by
  let := (SuzukiContainment.reduced_hypothesis h).finite_parabolic i
  rw [← reduced_residual_map_inclusion h i, map_map]
  have hf : f.comp (inclusion (SuzukiContainment.reduced_parabolic_le h i)) =
      (MulAut.conj.comp Q.subtype).comp e.toMonoidHom := MonoidHom.ext he
  rw [hf, ← map_map, map_solvableResidual_eq _ e.surjective, map_map]

private theorem endpoint_range {X Y : Type*} [Group X] [Group Y]
    (Q : Subgroup X) (f : Y ≃* Q) :
    (Q.subtype.comp f.toMonoidHom).range = Q := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ f.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

/-- Extend both reduced residual markings to the original full endpoints,
retaining the supplied endpoint maps, inner intersections and full overlap. -/
def residualMarkingOfRestoredIso
    {G X : Type*} [Group G] [Group X] {L R S : Subgroup G}
    (h : HypothesisF11 ![L,R] S) {P Q : Subgroup X}
    (U : SourceCompletion.UnitaryNonbinary.SourceExtension P Q)
    (E : Iso (originalAmalgam ![L,R] S) U.amalgam)
    (e₀ : parabolic ![L,R] (SuzukiContainment.reducedSylow ![L,R] S) 0 ≃* P)
    (e₁ : parabolic ![L,R] (SuzukiContainment.reducedSylow ![L,R] S) 1 ≃* Q)
    (hl : ∀ x, (E.left (inclusion (SuzukiContainment.reduced_parabolic_le h 0) x)).val =
      MulAut.conj (e₀ x).val)
    (hr : ∀ x, (E.right (inclusion (SuzukiContainment.reduced_parabolic_le h 1) x)).val =
      MulAut.conj (e₁ x).val) :
    Global.OriginalExtension.Marking L R S
      ((solvableResidual P).map P.subtype) ((solvableResidual Q).map Q.subtype) P Q := by
  let J : Iso (Global.sourceParabolicAmalgam ![L,R] S) (originalAmalgam ![L,R] S) := {
    left := MulEquiv.refl _
    right := MulEquiv.refl _
    middle := MulEquiv.subgroupCongr (lemma_F_1_3_6 h)
    left_commutes := fun _ => rfl
    right_commutes := fun _ => rfl }
  let F := J.trans E
  let f₀ := U.left.subtype.comp F.left.toMonoidHom
  let f₁ := U.right.subtype.comp F.right.toMonoidHom
  have hf₀ : f₀.range = U.left := endpoint_range _ F.left
  have hf₁ : f₁.range = U.right := endpoint_range _ F.right
  refine { left := f₀, right := f₁
           left_injective := Subtype.val_injective.comp F.left.injective
           right_injective := Subtype.val_injective.comp F.right.injective
           agrees := ?_
           left_residual := residual_image_of_restriction h 0 P f₀ e₀ hl
           right_residual := residual_image_of_restriction h 1 Q f₁ e₁ hr
           left_base := ?_, right_base := ?_, whole_overlap := ?_ }
  · intro x
    exact (congrArg Subtype.val (F.left_commutes x)).trans
      (congrArg Subtype.val (F.right_commutes x)).symm
  · rw [hf₀]
    exact U.left_inner
  · rw [hf₁]
    exact U.right_inner
  · have he : f₀.comp (Global.sourceParabolicAmalgam ![L,R] S).left =
        U.middle.subtype.comp F.middle.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact congrArg Subtype.val (F.left_commutes x)
    rw [he, endpoint_range, hf₀, hf₁]

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
