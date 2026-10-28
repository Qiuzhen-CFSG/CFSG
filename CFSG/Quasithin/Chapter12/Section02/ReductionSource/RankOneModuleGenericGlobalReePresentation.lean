module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReePresentation.FullComparison
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReePresentation.SignedComparison
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobal

/-!
# Full marked Ree presentation in the original Chapter 12 preparation

The actual Hypothesis1221, many-overgroups hypothesis, selected factor and
Preparation supply genuine F.1.1. Finite positive, full-Cartan, literal Weyl,
signed-root and Gauss equations on the same marked quotient construct the
full Ree equivalence and both oriented parabolic comparisons. The final
application supplies ConcreteAmalgamComparison.ree for the literal
hcomparison consumer, preserving the whole original common-Borel square.
Earlier positive, Borel, normalizer and opposite-root applications remain
available unchanged. Every m, including the full binary Model 0, is retained.

Source fields, compatible parameters, verification of the finite equations
and exhaustive row selection remain with split recognition and final source
assembly. Binary type alternatives alone do not supply these marked data.
Source: DGS Theorem D, p.224; Aschbacher--Smith 12.2.2, p.795, and F.1.1--3;
GLS3 2.3--2.4 and Steinberg section 11.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)

include D in
/-- On the actual prepared Chapter 12 pair, the finite positive Ree equations
give a full common-Sylow isomorphism and both original endpoint squares.
The model parameter is unrestricted, so this also compares the full binary U. -/
theorem rankOne_ree_positive_presentation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (preparation : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    {m : ℕ} (d : SourcePositive.Charts Q split m) (E : SourceAngular.Equations Q split d)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam) :
    ∃ f : Global.sourceS L H ≃* ReeF4.Parabolics.unipotent m,
      (∀ (u : ReeF4.Parabolics.unipotent m) (i : Fin 2),
        MarkedLocal.endpointMap Q e i
          ⟨f.symm u, (show Global.sourceS L H ≤
            ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i from
              le_sup_right.trans le_sup_left) (f.symm u).property⟩ =
            ((SourceAngular.comparison Q split d E).symm u : X ⧸ Q.D)) ∧
      Nat.card (Global.sourceS L H) = Nat.card (ReeF4.Parabolics.unipotent m) := by
  have hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
  let f := ReePresentation.originalUnipotentEquiv Q e hf split d E
  exact ⟨f, ReePresentation.originalUnipotentEquiv_endpoint Q e hf split d E,
    Nat.card_congr f.toEquiv⟩

include D in
/-- The original whole-overlap comparison, retaining both endpoint inclusion
squares, follows from the finite positive and full-Cartan equations. -/
theorem rankOne_ree_borel_presentation
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
        inf_le_left inf_le_right) Q.standardAmalgam) :
    let hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
    ∃ f : ChapterF.Source.commonBorel ![L,R] (Global.sourceS L H) ≃* ReeF4.Parabolics.borel m,
      (∀ b, (SourceBorel.comparison Q split d E torus (f b) : X ⧸ Q.D) =
        MarkedLocal.borelMap Q e hf b) ∧
      (∀ (b : ChapterF.Source.commonBorel ![L,R] (Global.sourceS L H)) (i : Fin 2),
        MarkedLocal.endpointMap Q e i
        ⟨b, ChapterF.Source.commonBorel_le_parabolic i b.property⟩ =
          (SourceBorel.comparison Q split d E torus (f b) : X ⧸ Q.D)) := by
  dsimp only
  let hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
  exact ⟨ReePresentation.originalBorelEquiv Q e hf split d E torus,
    ReePresentation.originalBorelEquiv_square Q e hf split d E torus,
    ReePresentation.originalBorelEquiv_endpoint Q e hf split d E torus⟩

include D in
/-- The finite literal Weyl and full-Cartan equations identify the entire
normalizer on the actual Chapter 12 quotient. Both original endpoint squares
agree with this map on the whole Cartan, including in the binary field. -/
theorem rankOne_ree_normalizer_presentation
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
    (W : SourceNormalizer.WeylData Q split d torus)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam) :
    let hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
    ∃ f : ReeF4.SectionGeometry.BNPair.normalizerWords m ≃* Q.tits.N,
      (∀ s, f (ReeF4.SectionGeometry.BNPair.simpleLift m
        (NormalizerPresentation.side s)) = W.n s) ∧
      (∀ (t : ReeF4.Parabolics.fixedTorus m) (i : Fin 2),
        MarkedLocal.endpointMap Q e i
          ⟨ReePresentation.originalCartanLift Q e hf split d E torus t,
            ChapterF.Source.commonBorel_le_parabolic i
              (ReePresentation.originalCartanLift Q e hf split d E torus t).property⟩ =
          (f ⟨t,ReeF4.SectionGeometry.BNPair.fixedTorus_le_normalizerWords m t.property⟩ : X ⧸ Q.D)) := by
  dsimp only
  let hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
  exact ⟨SourceNormalizer.comparison Q split d torus W,
    SourceNormalizer.comparison_simple Q split d torus W,
    ReePresentation.originalCartanLift_endpoint Q e hf split d E torus W⟩

include D in
/-- Finite signed Weyl equations give injective lifts of both complete native
opposite simple roots to the literal prepared Chapter 12 endpoints. The
source quotient and the original or geometric marking are unchanged. -/
theorem rankOne_ree_signed_root_presentation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (preparation : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    {m : ℕ} (d : SourcePositive.Charts Q split m)
    (torus : SourceBorel.TorusData Q split d)
    (W : SourceNormalizer.WeylData Q split d torus)
    (signed : SourceSigned.Equations Q split d torus W)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam) :
    ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H) ∧
    ∃ f : (s : Bool) →
        rootBlock m (NormalizerPresentation.side s) false →*
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H)
            (SourceNormalizer.index d.orientation s),
      (∀ s, Function.Injective (f s)) ∧
      (∀ s a, MarkedLocal.endpointMap Q e (SourceNormalizer.index d.orientation s) (f s a) =
        (SourceSigned.comparison Q split d torus W false (SourceSigned.simpleIndex s)
          (SignedCharts.simpleRootEquiv m false s a) : X ⧸ Q.D)) := by
  refine ⟨(D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1,
    ReePresentation.originalNegativeBlockLift Q e split d torus W signed, ?_, ?_⟩
  · exact ReePresentation.originalNegativeBlockLift_injective Q e split d torus W signed
  · exact ReePresentation.originalNegativeBlockLift_square Q e split d torus W signed

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open ReeF4.RootPresentationRecognition
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)

/-- The finite Ree equations supply the literal `hcomparison` catalogue
premise for the selected Chapter 12 preparation, together with the formula
on its entire original common Borel. No positive-parameter restriction is used.
Source construction and exhaustive selection of these data remain separate. -/
theorem rankOne_ree_marked_presentation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (preparation : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    {m : ℕ} (d : SourcePositive.Charts Q split m)
    (torus : SourceBorel.TorusData Q split d) (weyl : SourceNormalizer.WeylData Q split d torus)
    (positive : SourceAngular.Equations Q split d) (signed : SourceSigned.Equations Q split d torus weyl)
    (gauss : ReeF4.RootPresentationRecognition.Global.SourceGauss Q split d torus weyl)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
    (let hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
     ∀ b : ChapterF.Source.commonBorel ![L,R] (Global.sourceS L H),
       ((ReePresentation.comparison Q e split d torus weyl positive signed gauss).middle
         ((MulEquiv.subgroupCongr (ChapterF.Source.lemma_F_1_3_6 hf).symm) b) : ReeF4.Model m) =
           ReePresentation.quotientEquiv Q split d torus weyl positive signed gauss
             (MarkedLocal.borelMap Q e hf b)) := by
  refine ⟨Global.ConcreteAmalgamComparison.ree m
    (ReePresentation.concrete_comparison Q e split d torus weyl positive signed gauss),?_⟩
  dsimp only
  exact ReePresentation.comparison_commonBorel_apply Q e split d torus weyl positive signed gauss _

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
