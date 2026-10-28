module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2WeylLocalization
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2WeylTorus

/-!
# Torus centralizers and Weyl localization in the original Chapter12 pair

The whole-overlap torus is self-centralizing inside each of the actual two
parabolics, including at field four. Consequently the canonical sixth power
vanishes exactly when it belongs to either parabolic. The existing completion
recognition then gives an actual G₂ model at the original exponent n > 1.

Placement of that power remains an ambient source obligation. These results
do not discharge it or construct the exhaustive comparison and original
uniqueness needed for the full generic/global exit.
Source: Aschbacher–Smith F.4.24–26, printed pp.287–288, and 5.3.3–4, p.659,
with the Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Global.G2CompletionGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal marked torus is self-centralizing inside both original parabolics. -/
theorem rankOne_global_g2_parabolic_torus_centralizers
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    ∀ i : Fin 2, ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i ⊓
      centralizer (Global.g2MarkedTorus e : Set G) = Global.g2MarkedTorus e :=
  d.g2_parabolic_torus_centralizers (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F e

/-- A nontrivial canonical sixth power must escape both actual parabolics. -/
theorem rankOne_global_g2_weyl_localization
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    let w := (e.right.symm (nativeS (F := F))).val *
      (e.left.symm (nativeR (F := F))).val
    (∃ i : Fin 2, w^6 ∈ ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i) ↔
      w^6=1 :=
  d.g2_weyl_localization (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F e

/-- The localized sixth power yields an actual rank-two model with n > 1.
The source assembly must still prove the displayed placement hypothesis. -/
theorem rankOne_globalExit_of_g2_weyl_localized
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hw : ∃ i : Fin 2,
      ((e.right.symm (nativeS (F := F))).val * (e.left.symm (nativeR (F := F))).val)^6 ∈
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i) :
    RankOneModule.GlobalExit G := by
  obtain ⟨hF,hiso⟩ := d.g2_ambient_recognition_of_weyl_localized
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F e hw
  exact Or.inl ⟨n,hn,ClassificationModels.IsRankTwoModel.g2 hn
    ⟨F,inferInstance,inferInstance,hF,hiso⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
