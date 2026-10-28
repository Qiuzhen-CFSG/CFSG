module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.MarkedRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobal

/-!
# Chapter 12 application of the full marked source A₂ recognition

The original Chapter 12 preparation supplies F.1.1 for its actual local pair.
The source natural actions and an independently marked m=3 quotient then
construct all six compatible roots and the full PSL₃ amalgam comparison.
Both original endpoint maps and the entire common Borel map are preserved,
with the actual Sylow image and either orientation. No root-data, model
isomorphism or perfect-factor hypothesis is required.

Source: AS Chapter 12, section 2 and F.1.1--3; DGS, Groups and Graphs,
10.5 and Theorem D, printed pp.156,224. Earlier natural-action and apartment
premises retain their source-assembly producers.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Configuration
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Matrix.PSL3.RootPresentationRecognition
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source
open ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance a2MarkedApplicationFieldAlgebra {K : Type*} [Field K] [CharP K 2] :
    Algebra (ZMod 2) K := ZMod.algebra K 2

include D in
/-- The Chapter 12 preparation plus the genuine source natural actions gives the
full original marked A₂ comparison; root relations and generation are proved internally. -/
theorem rankOne_a2_marked_source_recognition
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (prep : Global.Preparation T L H A B R)
    {X : Type*} [Group X] {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic ![L,R] (Global.sourceS L H) 0)
        (parabolic ![L,R] (Global.sourceS L H) 0 ⊓ parabolic ![L,R] (Global.sourceS L H) 1)
        (parabolic ![L,R] (Global.sourceS L H) 1) inf_le_left inf_le_right) d.standardAmalgam)
    (split : SplitData d.tits)
    (c₀ : BOneActionData (fullFamily ![L,R] (Global.sourceS L H))
      (CosetGeometry.base (fullFamily ![L,R] (Global.sourceS L H)) false)
      (CosetGeometry.base (fullFamily ![L,R] (Global.sourceS L H)) true) k₀ W₀)
    (c₁ : BOneActionData (fullFamily ![L,R] (Global.sourceS L H))
      (CosetGeometry.base (fullFamily ![L,R] (Global.sourceS L H)) true)
      (CosetGeometry.base (fullFamily ![L,R] (Global.sourceS L H)) false) k₁ W₁)
    (hn₀ : (commonBorel ![L,R] (Global.sourceS L H)).subgroupOf
      (generated ![L,R] (Global.sourceS L H)) ≤ normalizer (c₀.actor : Set _))
    (hn₁ : (commonBorel ![L,R] (Global.sourceS L H)).subgroupOf
      (generated ![L,R] (Global.sourceS L H)) ≤ normalizer (c₁.actor : Set _))
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hm : RootCoordinates.rotationOrder d = 3) (hc : centerIn c₁.actor = ⊥) :
    ∃ (i : Fin 2) (e : (X ⧸ d.D) ≃* PSL(3,k₁))
      (cmp : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic ![L,R] (Global.sourceS L H) 0)
          (parabolic ![L,R] (Global.sourceS L H) 0 ⊓ parabolic ![L,R] (Global.sourceS L H) 1)
          (parabolic ![L,R] (Global.sourceS L H) 1) inf_le_left inf_le_right)
        (flagAmalgam k₁ i)),
      (∀ a, (cmp.left a : PSL(3,k₁)) = e (mark.left a : X ⧸ d.D)) ∧
      (∀ b, (cmp.middle b : PSL(3,k₁)) = e (mark.middle b : X ⧸ d.D)) ∧
      (∀ a, (cmp.right a : PSL(3,k₁)) = e (mark.right a : X ⧸ d.D)) ∧
      split.U.map e.toMonoidHom = Matrix.PSL3.LinearThree.unipotent k₁ := by
  have hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH prep).1
  refine ⟨A2Source.MarkedRecognition.pointIndex d mark hf c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split,
    A2Source.MarkedRecognition.quotientEquiv d mark hf c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split,
    A2Source.MarkedRecognition.comparison d mark hf c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split,
    A2Source.MarkedRecognition.comparison_left_apply d mark hf c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split,
    A2Source.MarkedRecognition.comparison_middle_apply d mark hf c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split,
    A2Source.MarkedRecognition.comparison_right_apply d mark hf c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split,?_⟩
  have hs := A2Source.MarkedRecognition.source_sylow_image d mark hf c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split
  rwa [MarkedLocal.sylow_range d mark hf split] at hs

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
