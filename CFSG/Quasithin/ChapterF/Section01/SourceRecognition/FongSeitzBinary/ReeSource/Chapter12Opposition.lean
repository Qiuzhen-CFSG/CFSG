module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.WeylData
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReePresentation

/-!
# Actual Chapter 12 consumer of the source opposition argument

On the selected factor and its original Preparation, source opposition
constructs the presentation's Weyl-data input. The existing Chapter 12
normalizer comparison now needs only the remaining source root equations,
full torus and its two field-action equations; it no longer assumes either
simple-lift squares or their mixed eighth-power equation. The whole Cartan
and both original endpoint squares are retained on the same Q.

This is an intermediate normalizer application. The rank-one pairing,
odd-degree discharge, full section-10 coordinate equations and final
ConcreteAmalgamComparison.ree are still required for source recognition.
Source: Fong--Seitz I (6H), p.51; II section 10, p.232; AS 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.ReeSource
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)

include D in
/-- Apply the literal Chapter 12 normalizer comparison with the source-proved
Weyl relations, preserving the original hypotheses and endpoint squares. -/
theorem rankOne_ree_normalizer_of_source_opposition
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (preparation : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    {m : ℕ} (d : SourcePositive.Charts Q split m) (E : SourceAngular.Equations Q split d)
    (torus : SourceBorel.TorusData Q split d)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam)
    (hnOdd : Odd n)
    (μ₀ : (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⧸
      originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 0) ≃*
        BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup n)
    (T₀ : Sylow 2 (BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup n))
    (hB₀ : (originalFaithfulBorel (L := ![L,R]) (S := Global.sourceS L H) 0).map
      μ₀.toMonoidHom = normalizer (T₀ : Set _))
    (μ₁ : (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1 ⧸
      originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 1) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hB₁ : (originalFaithfulBorel (L := ![L,R]) (S := Global.sourceS L H) 1).map
      μ₁.toMonoidHom = normalizer (BenderSuzuki.MatrixGroups.SuzukiRootSubgroup m : Set _))
    (s : ∀ i, Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource.RootReflection Q split i)
    (hact : ∀ b (a : (ReeF4.CoefficientField m)ˣ × (ReeF4.CoefficientField m)ˣ),
      (sourceWeylLift Q split s d.orientation b : X ⧸ Q.D) * torus.h a *
        (sourceWeylLift Q split s d.orientation b : X ⧸ Q.D)⁻¹ =
        torus.h (NormalizerTables.table m b a)) :
    let hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
    ∃ f : ReeF4.SectionGeometry.BNPair.normalizerWords m ≃* Q.tits.N,
      (∀ b, f (ReeF4.SectionGeometry.BNPair.simpleLift m
        (NormalizerPresentation.side b)) = sourceWeylLift Q split s d.orientation b) ∧
      (∀ (t : ReeF4.Parabolics.fixedTorus m) (i : Fin 2),
        MarkedLocal.endpointMap Q e i
          ⟨ReePresentation.originalCartanLift Q e hf split d E torus t,
            ChapterF.Source.commonBorel_le_parabolic i
              (ReePresentation.originalCartanLift Q e hf split d E torus t).property⟩ =
          (f ⟨t,ReeF4.SectionGeometry.BNPair.fixedTorus_le_normalizerWords m t.property⟩ : X ⧸ Q.D)) := by
  let hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
  exact D.rankOne_ree_normalizer_presentation h hmany hn hpsl hH preparation Q split d E torus
    (originalReeWeylData Q e hf split d.rotation_eight n hnOdd m μ₀ T₀ hB₀ μ₁ hB₁ s d torus hact) e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
