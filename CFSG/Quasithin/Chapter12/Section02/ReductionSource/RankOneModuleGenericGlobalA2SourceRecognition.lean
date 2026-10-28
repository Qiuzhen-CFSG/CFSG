module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobal

/-!
# Original A₂ source recognition in the actual Chapter 12 preparation

The preparation supplies genuine F.1.1. The original natural actions,
centerfree branch, and same m=3 SourceQuotient then construct the six-root
recognition and full marked comparison internally. Both endpoint formulas
and the whole common-Borel formula retain the literal original projection,
and the source U has exactly the native unipotent image.

The source natural-action and apartment premises remain explicit. The
independent marking is handled by RankOneModuleGenericGlobalA2MarkedRecognition.
This does not assume RootData, a model isomorphism, or perfect local factors.
Source: DGS, Groups and Graphs, 10.5 and Theorem D, pp.156,224;
Aschbacher--Smith 12.2.2, p.795, and F.1.1--3.
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
local instance a2SourceApplicationFieldAlgebra {K : Type*} [Field K] [CharP K 2] :
    Algebra (ZMod 2) K := ZMod.algebra K 2

include D in
/-- The Chapter 12 preparation plus the genuine source natural actions gives the
full original marked A₂ comparison; root relations and generation are proved internally. -/
theorem rankOne_a2_source_recognition
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (prep : Global.Preparation T L H A B R)
    (d : SourceQuotient ![L,R] (Global.sourceS L H)) (split : SplitData d.tits)
    (c₀ : BOneActionData (fullFamily ![L,R] (Global.sourceS L H))
      (base (fullFamily ![L,R] (Global.sourceS L H)) false)
      (base (fullFamily ![L,R] (Global.sourceS L H)) true) k₀ W₀)
    (c₁ : BOneActionData (fullFamily ![L,R] (Global.sourceS L H))
      (base (fullFamily ![L,R] (Global.sourceS L H)) true)
      (base (fullFamily ![L,R] (Global.sourceS L H)) false) k₁ W₁)
    (hn₀ : (commonBorel ![L,R] (Global.sourceS L H)).subgroupOf
      (generated ![L,R] (Global.sourceS L H)) ≤ normalizer (c₀.actor : Set _))
    (hn₁ : (commonBorel ![L,R] (Global.sourceS L H)).subgroupOf
      (generated ![L,R] (Global.sourceS L H)) ≤ normalizer (c₁.actor : Set _))
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hm : RootCoordinates.rotationOrder d = 3) (hc : centerIn c₁.actor = ⊥) :
    ∃ (i : Fin 2) (e : ((generated ![L,R] (Global.sourceS L H)) ⧸ d.D) ≃* PSL(3,k₁))
      (cmp : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic ![L,R] (Global.sourceS L H) 0)
          (parabolic ![L,R] (Global.sourceS L H) 0 ⊓ parabolic ![L,R] (Global.sourceS L H) 1)
          (parabolic ![L,R] (Global.sourceS L H) 1) inf_le_left inf_le_right)
        (flagAmalgam k₁ i)),
      (∀ a, (cmp.left a : PSL(3,k₁)) = e (d.q ⟨a,parabolic_le_generated 0 a.property⟩)) ∧
      (∀ b, (cmp.middle b : PSL(3,k₁)) = e (d.q ⟨b,parabolic_le_generated 0 b.property.1⟩)) ∧
      (∀ a, (cmp.right a : PSL(3,k₁)) = e (d.q ⟨a,parabolic_le_generated 1 a.property⟩)) ∧
      split.U.map e.toMonoidHom = Matrix.PSL3.LinearThree.unipotent k₁ := by
  have hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH prep).1
  refine ⟨A2Source.Recognition.pointIndex hf d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split,
    A2Source.Recognition.quotientEquiv hf d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split,
    A2Source.Recognition.comparison hf d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split,
    A2Source.Recognition.comparison_left_apply hf d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split,
    A2Source.Recognition.comparison_middle_apply hf d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split,
    A2Source.Recognition.comparison_right_apply hf d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split,?_⟩
  have hs := A2Source.Recognition.source_sylow_image hf d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split
  rwa [MarkedLocal.sylow_range d (originalMarkedIso d) hf split] at hs

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
