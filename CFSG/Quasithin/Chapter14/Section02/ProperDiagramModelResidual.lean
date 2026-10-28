module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramResidual
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSubgroups
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectSubgroups
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup

/-!
# Rank-one quotients of the marked parabolic residuals

For each nonbinary diagram model, the actual perfect residual of the
parabolic preimage has quotient PSL₂ by its two-core. The central-cover
comparison reduces this to the matrix parabolic residual. Its nonsolvable
SL₂ quotient also proves that the selected residual is outside the original
maximal subgroup marked by the Borel.

Source: Aschbacher–Smith, 14.2.8(3), printed p.983.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE ChapterE.Structure
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

private noncomputable def residualEquivLocal {D : Type*} [Group D] [Finite D]
    (P L : Subgroup D) (h : (solvableResidual P).map P.subtype = L) :
    solvableResidual P ≃* L :=
  ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
    (MulEquiv.subgroupCongr h)

noncomputable def originalLinearParabolicResidualCoreEquiv
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K)) (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hcard : 4 ≤ Nat.card F)
    (e : sourceImage (ChapterB.minimalParabolicMax T hP) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :
    (markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e
      (Matrix.PSL3.LinearThree.pointParabolic F) ⧸
      pCore 2 (markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e
        (Matrix.PSL3.LinearThree.pointParabolic F))) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := by
  let d := residualEquivLocal _ _
    (Matrix.PSL3.LinearThree.PerfectSubgroups.pointParabolic_residual F hcard)
  have hr : ∀ p : ℕ, p.Prime → Odd p →
      primeRank p (solvableResidual (Matrix.PSL3.LinearThree.pointParabolic F)) ≤ 1 := by
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [primeRank_equiv p d]
    exact Matrix.PSL3.LinearThree.PerfectSubgroups.pointLocal_odd_primeRank_le_one F ho
  exact (originalParabolicResidualCoreEquiv T hP hs K hK hqK hgen e _ hr).trans
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans
      ((Matrix.PSL3.LinearThree.pointLocalCoreQuotientEquiv F).trans
        (Theory.PSL2.sl2QuotientEquiv F)))

noncomputable def originalSymplecticParabolicResidualCoreEquiv
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K)) (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hcard : Nat.card F = 2^f) (hf : 1 < f)
    (e : sourceImage (ChapterB.minimalParabolicMax T hP) K ≃*
      Theory.SpecificGroups.SymplecticFour.Sp F) :
    (markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e
      (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)) ⧸
      pCore 2 (markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e
        (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)))) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := by
  let d := residualEquivLocal _ _
    (Theory.SpecificGroups.SymplecticFour.pointParabolic_solvableResidual_eq hcard hf)
  have hr : ∀ p : ℕ, p.Prime → Odd p →
      primeRank p (solvableResidual
        (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F))) ≤ 1 := by
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [primeRank_equiv p d]
    exact Theory.SpecificGroups.SymplecticFour.pointLocal_odd_primeRank_le_one ho
  exact (originalParabolicResidualCoreEquiv T hP hs K hK hqK hgen e _ hr).trans
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans
      ((Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hcard hf).trans
        (Theory.PSL2.sl2QuotientEquiv F)))

private theorem nonsolvable_local_not_le {D L : Type*} [Group D] [Group L]
    [Group.IsPerfect L] [Nontrivial L] (A B : Subgroup D) [Group.IsSolvable B]
    (q : A →* L) (hq : Function.Surjective q) : ¬ A ≤ B := by
  intro hle
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  exact Group.IsPerfect.not_isSolvable L (Group.isSolvable_of_surjective hq)

theorem originalLinearParabolicResidual_not_le
    (M K : Subgroup H) {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hcard : Nat.card F = 2^f) (hf : 1 < f)
    (e : sourceImage M K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap M K).map e.toMonoidHom = Matrix.PSL3.LinearThree.borel F) :
    ¬ markedParabolicResidual M K e (Matrix.PSL3.LinearThree.pointParabolic F) ≤ M := by
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ f)
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := by
    let t := Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) (1 : F)
    refine ⟨⟨t, 1, ?_⟩⟩
    intro heq
    have hh := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g.val 0 1) heq
    simp [t, Matrix.SpecialLinearGroup.transvection_coe] at hh
  let := GorensteinWalter.sl2_isPerfect_of_card_gt_three F (by omega)
  let := Matrix.PSL3.LinearThree.BorelStructure.borel_isSolvable F hcard
  apply markedParabolicResidual_not_le M K e _ _ he
  rw [Matrix.PSL3.LinearThree.PerfectSubgroups.pointParabolic_residual F h4]
  let d := Matrix.PSL3.LinearThree.pointLocalCoreQuotientEquiv F
  exact nonsolvable_local_not_le _ _
    (d.toMonoidHom.comp (QuotientGroup.mk' _))
    (d.surjective.comp (QuotientGroup.mk'_surjective _))

theorem originalSymplecticParabolicResidual_not_le
    (M K : Subgroup H) {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hcard : Nat.card F = 2^f) (hf : 1 < f)
    (e : sourceImage M K ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (he : (componentOverlap M K).map e.toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.borel (F := F)) :
    ¬ markedParabolicResidual M K e
      (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)) ≤ M := by
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ f)
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := by
    let t := Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) (1 : F)
    refine ⟨⟨t, 1, ?_⟩⟩
    intro heq
    have hh := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g.val 0 1) heq
    simp [t, Matrix.SpecialLinearGroup.transvection_coe] at hh
  let := GorensteinWalter.sl2_isPerfect_of_card_gt_three F (by omega)
  let := Theory.SpecificGroups.SymplecticFour.isSolvable_borel hcard
  apply markedParabolicResidual_not_le M K e _ _ he
  rw [Theory.SpecificGroups.SymplecticFour.pointParabolic_solvableResidual_eq hcard hf]
  let d := Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hcard hf
  exact nonsolvable_local_not_le _ _
    (d.toMonoidHom.comp (QuotientGroup.mk' _))
    (d.surjective.comp (QuotientGroup.mk'_surjective _))
end CFSG.Quasithin.Chapter14.Section02
