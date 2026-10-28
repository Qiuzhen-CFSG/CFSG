module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Chapter12SixH
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalV1Natural

/-!
# Chapter 12 consumer for the natural first linear layer

The Section 10 owner proves the natural action on the literal original
quotient `U_s₁ / X₁`, including the binary case. This module applies that
result to the actual Chapter 12 pair supplied by `Global.Preparation`.
It retains the original `Hypothesis1221`, `KnownSimple`, `HStar`, PSL₂ and
whole-Borel markings, and exposes the endpoint transport needed by the
source basis consumer. No mixed equation, torus, signed or Gauss relation is
assumed here; those remain with the Section 10 coordinate owner.

Source: Fong--Seitz II (1974), printed pp.222--223; Chapter 12, Section 2.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.ReeSource
open ChapterF.Source.FongSeitzBinary.ReeSection10

variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
variable
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (preparation : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : RootCoordinates.rotationOrder Q = 8) (m : ℕ)
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

local instance chapter12V1BinaryAlgebra :
    Algebra (ZMod 2) (ReeF4.CoefficientField m) := ZMod.algebra _ 2

include D h hmany hn hpsl hH preparation Q split hm e hnOdd μ₀ T₀ hB₀ μ₁ hB₁ in
/-- Conjugation by the selected first endpoint is the pinned natural action. -/
theorem rankOne_ree_original_v1_action
    (g : ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
    (hg : MarkedLocal.endpointMap Q e 0 g ∈
      rankOne Q split 0)
    (v : pCore 2 (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)) :
    originalV1Coordinates Q e split
        (D.rankOneReeSixHData h hmany hn hpsl hH preparation Q split hm m e
          hnOdd μ₀ T₀ hB₀ μ₁ hB₁)
        (Additive.ofMul (QuotientGroup.mk (MulAut.conjNormal g v))) =
      Representation.SL2.BinarySmall.natural
        ((linearPinning Q split
          (D.rankOneReeSixHData h hmany hn hpsl hH preparation Q split hm m e
            hnOdd μ₀ T₀ hB₀ μ₁ hB₁)).symm ⟨MarkedLocal.endpointMap Q e 0 g,hg⟩)
        (originalV1Coordinates Q e split
          (D.rankOneReeSixHData h hmany hn hpsl hH preparation Q split hm m e
            hnOdd μ₀ T₀ hB₀ μ₁ hB₁)
          (Additive.ofMul (QuotientGroup.mk v))) := by
  exact originalV1Coordinates_conjugation Q e split
    (D.rankOneReeSixHData h hmany hn hpsl hH preparation Q split hm m e hnOdd μ₀ T₀ hB₀ μ₁ hB₁)
    g hg v

include D h hmany hn hpsl hH preparation Q split hm e hnOdd μ₀ T₀ hB₀ μ₁ hB₁ in
/-- The same natural vector has both literal endpoint images. -/
theorem rankOne_ree_original_v1_endpoints
    (v : pCore 2 (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)) :
    ∀ i : Fin 2, ∃ hi :
        (v.val.val : G) ∈ ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i,
      MarkedLocal.endpointMap Q e i ⟨v.val.val,hi⟩ =
        (originalV1NumeratorEquiv Q e split
          (D.rankOneReeSixHData h hmany hn hpsl hH preparation Q split hm m e
            hnOdd μ₀ T₀ hB₀ μ₁ hB₁) v : X ⧸ Q.D) ∧
      originalV1Coordinates Q e split
          (D.rankOneReeSixHData h hmany hn hpsl hH preparation Q split hm m e
            hnOdd μ₀ T₀ hB₀ μ₁ hB₁)
          (Additive.ofMul (QuotientGroup.mk v)) =
        V1Coordinates Q split
          (D.rankOneReeSixHData h hmany hn hpsl hH preparation Q split hm m e
            hnOdd μ₀ T₀ hB₀ μ₁ hB₁)
          (Additive.ofMul (QuotientGroup.mk
            (originalV1NumeratorEquiv Q e split
              (D.rankOneReeSixHData h hmany hn hpsl hH preparation Q split hm m e
                hnOdd μ₀ T₀ hB₀ μ₁ hB₁) v))) := by
  exact originalV1Coordinates_endpoints Q e split
    (D.rankOneReeSixHData h hmany hn hpsl hH preparation Q split hm m e hnOdd μ₀ T₀ hB₀ μ₁ hB₁)
    (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1 v

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
