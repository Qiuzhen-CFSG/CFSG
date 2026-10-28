module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.G2Native
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ResidualMarking
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ReducedSolvability
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.G2

/-!
# Reduced G₂ recognition on the original selected pair

Native lifting and equality of the embedded reduced and original residuals
construct the full original marking. The original normalized Borel then
places the same S in R and removes the outer extension. The original quotient
marks fix the field and the orientation. The binary field is excluded using
the solvable reduced short parabolic before invoking any native lift.

Source: DGS (1985), (15.2), pp.226–228; Aschbacher–Smith F.1.12,
pp.263–264, and 5.2.6, pp.650–651. Reduced recognition remains explicit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open Chapter6.Source.RankOneGeneric Atlas.G2 Atlas.G2.LieParabolicSetup

theorem exists_original_g2_marking_of_reduced_iso
    {G : Type*} [Group G] {L R S : Subgroup G} (h : HypothesisF11 ![L,R] S)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (short : Bool)
    (e : Iso (reducedAmalgam ![L,R] S) (G2Native.amalgam F short)) :
    Nonempty (Global.OriginalG2.Marking F short L R S) := by
  obtain ⟨E,f,hl,hr,_⟩ := G2Native.exists_original_extension_iso F h hq short e
  have hres (b : Bool) :
      (solvableResidual (G2Native.endpoint F b)).map (G2Native.endpoint F b).subtype =
        Global.OriginalG2.localFactor F b := by
    cases b
    · exact HigherFieldResiduals.parabolic₂_residual hq
    · exact HigherFieldResiduals.parabolic₁_residual hq
  have hf := residualMarkingOfRestoredIso h E f e.left e.right hl hr
  rw [hres short,hres (!short)] at hf
  exact ⟨hf⟩

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (F : Type) [Field F] [Finite F] [CharP F 2] (short : Bool)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) (G2Native.amalgam F short))
include d h hTH hp e

/-- Original nonsolvability excludes the binary reduced row in both orientations. -/
theorem g2_reduced_parameter : 2 < Nat.card F := by
  by_contra hgt
  have htwo : Nat.card F = 2 := by have := Finite.one_lt_card (α := F); omega
  let : Group.IsSolvable (parabolic₁ (F := F)) := Global.G2Short.parabolic_solvable_of_card_two htwo
  cases short
  · let j : _ ≃* parabolic₁ (F := F) := e.right
    exact reduced_parabolics_not_solvable d h hTH hp 1
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)
  · let j : _ ≃* parabolic₁ (F := F) := e.left
    exact reduced_parabolics_not_solvable d h hTH hp 0
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)

/-- Restore the original right two-core and the same original containment S≤R. -/
theorem g2_original_core_and_containment_of_reduced_iso :
    (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R := by
  obtain ⟨f⟩ := exists_original_g2_marking_of_reduced_iso (d.hypothesisF11 h hTH)
    F (g2_reduced_parameter d h hTH hp F short e) short e
  exact ⟨d.original_g2_right_core h hTH hp F short f,
    d.sourceS_le_right_of_original_g2 h hTH hp F short f⟩

/-- Both original endpoint squares and the whole Borel are restored, and the
original quotient marks fix the field and both Sylow containments. -/
theorem g2_original_comparison_of_reduced_iso :
    Nonempty (Iso (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
      (Global.OriginalG2.orientedAmalgam F short)) ∧
      short = false ∧ Nat.card F = 2^n ∧
      (∀ i : Fin 2, Global.sourceS L H ≤ ![L,R] i) := by
  obtain ⟨f⟩ := exists_original_g2_marking_of_reduced_iso (d.hypothesisF11 h hTH)
    F (g2_reduced_parameter d h hTH hp F short e) short e
  exact ⟨⟨d.originalG2Comparison h hTH hp F short f⟩,
    d.original_g2_orientation h hTH hp F short f,
    d.original_g2_field_and_sylows h hTH hp F short f⟩

/-- Literal application discharging the original-marking premise of the catalogue. -/
theorem concreteComparison_of_reduced_g2 :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  obtain ⟨f⟩ := exists_original_g2_marking_of_reduced_iso (d.hypothesisF11 h hTH)
    F (g2_reduced_parameter d h hTH hp F short e) short e
  exact d.concreteComparison_of_original_g2 h hTH hp F short f

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
