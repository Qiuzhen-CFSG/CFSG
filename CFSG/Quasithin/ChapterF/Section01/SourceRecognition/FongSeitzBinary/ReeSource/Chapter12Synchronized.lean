module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Chapter12SixH
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalSynchronized

/-!
# Synchronized (10.8) at the selected Chapter 12 pair

Apply the original-Sylow pullback of (10.8) to the genuine F.1.1 pair
provided by the selected factor and Preparation. The natural full-Borel
markings, original KnownSimple/Hypothesis1221 assumptions and all parameters
m >= 0 are retained; no mixed-root equation is an input.
Source: Fong--Seitz II (1974), p.223; Aschbacher--Smith, Chapter 12, §2.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
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

/-- The synchronized mixed-root identity holds inside the selected original Sylow subgroup. -/
theorem rankOne_ree_synchronized_ten_eight (a b y z : ReeF4.CoefficientField m) :
    let hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
    let u := originalSynchronizedPoint Q e hf split hm n hnOdd m μ₀ T₀ hB₀ μ₁ hB₁
    (u (.inr 3) (y,z))⁻¹ * (u (.inr 0) (a,b))⁻¹ *
      u (.inr 3) (y,z) * u (.inr 0) (a,b) = u (.inl 1) (a*y) :=
  original_source_synchronized_ten_eight Q e
    (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
    split hm n hnOdd m μ₀ T₀ hB₀ μ₁ hB₁ a b y z

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
