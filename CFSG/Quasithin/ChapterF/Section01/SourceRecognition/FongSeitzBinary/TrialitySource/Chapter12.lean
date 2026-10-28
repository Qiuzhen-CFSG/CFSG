module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.SourceFieldApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialityPresentation.Chapter12

/-!
# Constructed triality recognition in the Chapter 12 chosen module

The original chosen-module preparation gives F.1.1. Construct the source
cubic field, compatible pinnings, all positive and signed relations and
literal Weyl placements from the earlier local models and structural row,
then apply the existing Chapter 12 marked-presentation consumer. The result
retains the original Sylow image, both odd Cartans and the whole Borel under
one ambient equivalence. The quotient may be geometric; no descent to the
original generated group is assumed.

KnownSimple and the original proper-K source boundary remain those of the
existing Chapter 12 consumer. Both endpoint orientations and every positive
binary triality exponent are retained, including q=2 and q=4.
Source: AS 12.2.2, printed p.795; F.1.1--12; DGS Theorem D.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Triality.Standard.RootPresentationRecognition
open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
variable {G X F K₀ : Type*} [Group G] [Finite G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field K₀] [Finite K₀]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)

open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups

include D in
/-- The chosen-module application now constructs the entire signed source
presentation from its genuine earlier local models and structural row. -/
theorem rankOne_triality_reconstructed
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (indices : Fin 2 ≃ Fin 2)
    (hVi : simpleRemainder Q split (indices 0) ≤ localKernel Q (indices 0))
    (hVj : simpleRemainder Q split (indices 1) ≤ localKernel Q (indices 1))
    (μi : localGroup Q split (indices 0) ≃* PSL(2,F))
    (μj : localGroup Q split (indices 1) ≃* PSL(2,K₀))
    (hm : rotationOrder Q = 6)
    (row : TrialitySource.StructuralRow Q split (indices 0) (indices 1))
    {m : ℕ} {hmpos : 0 < m} (hcard : Nat.card F = (2^m)^3) (hsmall : Nat.card K₀ = 2^m)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam) :
    ∃ roots : RootData Q split m hmpos (TrialitySource.SourceFieldApplication.sourceFrobenius F m) (indices 0),
      Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
      (MarkedLocal.sylowMap Q e
        (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH d).1).range.map
          roots.bruhat.quotientEquiv.toMonoidHom =
            _root_.Triality.Standard.Parabolics.unipotent (_root_.Triality.Standard.binaryParameters m hmpos) ∧
      ∀ i : Fin 2, Nat.Coprime 2 (Nat.card (MarkedLocal.localCartan Q e i)) ∧
        (MarkedLocal.localCartan Q e i).map
          (roots.bruhat.quotientEquiv.toMonoidHom.comp (MarkedLocal.factorMap Q e i)) ≤
            _root_.Triality.Standard.Parabolics.borel (_root_.Triality.Standard.binaryParameters m hmpos) := by
  let roots := TrialitySource.SourceFieldApplication.markedRootData (hn := hmpos) Q split indices hVi hVj μi μj
    hm row hcard hsmall e (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH d).1
  exact ⟨roots,D.rankOne_triality_marked_presentation h hmany hn hpsl hH d Q split roots e⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
