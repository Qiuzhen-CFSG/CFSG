module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2WeylTorus
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2CompletionGeometry

/-!
# The canonical Weyl product in the original Chapter12 pair

The same whole-overlap marking identifies the actual split torus. The two
source Weyl involutions have a product of order divisible by six, whose cube
inverts that torus and whose sixth power centralizes it. Thus a full ambient
torus-centralizer bound suffices for the concrete G₂ output at the original
exponent n > 1. The bound remains an explicit source obligation; these
statements do not complete the generic/global exit or its exhaustive comparison.

Source: Aschbacher–Smith F.4.8, F.4.26 and 5.3.3–4, printed pp.278,288,659,
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

/-- The canonical source Weyl product and its exact torus action, including F₄. -/
theorem rankOne_global_g2_weyl_torus_geometry
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
    Global.g2MarkedTorus e ≤
      ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H) ∧
      6 ∣ orderOf w ∧ 6 ≤ orderOf w ∧
      (∀ x∈Global.g2MarkedTorus e, MulAut.conj (w^3) x=x⁻¹) ∧
      w^6∈centralizer (Global.g2MarkedTorus e : Set G) :=
  d.g2_weyl_torus_geometry (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp e

/-- The full centralizer bound for the literal marked torus implies the
actual rank-two global output, with the original exponent restriction. -/
theorem rankOne_globalExit_of_g2_torus_centralizer
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
    (hC : centralizer (Global.g2MarkedTorus e : Set G) ≤ Global.g2MarkedTorus e) :
    RankOneModule.GlobalExit G := by
  obtain ⟨hF,hiso⟩ := d.g2_ambient_recognition_of_torus_centralizer
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp e hC
  exact Or.inl ⟨n,hn,ClassificationModels.IsRankTwoModel.g2 hn
    ⟨F,inferInstance,inferInstance,hF,hiso⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
