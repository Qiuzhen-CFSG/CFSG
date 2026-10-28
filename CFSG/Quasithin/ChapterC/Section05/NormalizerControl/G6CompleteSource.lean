module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.G6ControlSource
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.NormalizedCubicComplete
/-!
# The original A₃ normalizer and C.5.8 contradiction

The complete normalized-cubic G.6 source argument discharges the previously
explicit G.6 input on the literal C.5 quotient action. Only the genuine earlier
semisimple, A.3.6 and corrected B.4 source implications for the full known-simple
catalogue remain. The normalizer and final two-block contradiction retain all
original ambient QTKE, Sylow, block, and moving-element hypotheses.
Source: Aschbacher–Smith C.5.8 and C.5.12, printed pp.161–163.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource CounterexampleCharacteristic
open ChapterB.SourceInduction
open HighThreeRank.CoverCentralizer.SourceConstruction
universe u
variable {G : Type u} [Group G] [Finite G]

theorem alternating_three_control_from_original (T : Sylow 2 G) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (H R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (h' : RankOne.Setup R L F')
    (hKL : L ≤ centralizer (K : Set G))
    (hH : H = (K ⊔ L) ⊔ (T : Subgroup G)) (hHe : H ∈ Chapter1.He G)
    (hcoreU : H.pCoreIn 2 ≤ centralizer (RankOne.U K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (RankOne.U K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2) (hNK : T₁ ≤ normalizer (K : Set G))
    (hUorbit : RankOne.U K ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (hpair : ∀ g ∈ (T : Subgroup G), K.conjBy g = K ∨ K.conjBy g = L)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htout : t ∉ T₁) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G)) :
    let Y := normalizer (T₁ : Set G)
    let X := (pResidual 2 Y).map Y.subtype ⊔ (K ⊔ T₁)
    X ⊓ normalizer (T₁ : Set G) ≤ normalizer (RankOne.U K : Set G) :=
  alternating_three_control_from_original_of_g6 T hG
    (ChapterG.Section06.normalizedCubicSourceInput_knownSimple_of_earlier_classification hA h36 h4)
    H R K L T₁ hRT hTR h ha h' hKL hH hHe hcoreU hT₁ hhalf hNK hUorbit hpair
    t ht htout hKt x hx hxR hnc

theorem alternating_three_counterexample_false (T : Sylow 2 G) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (H R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (h' : RankOne.Setup R L F')
    (hKL : L ≤ centralizer (K : Set G))
    (hH : H = (K ⊔ L) ⊔ (T : Subgroup G)) (hHe : H ∈ Chapter1.He G)
    (hcoreU : H.pCoreIn 2 ≤ centralizer (RankOne.U K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (RankOne.U K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2) (hNK : T₁ ≤ normalizer (K : Set G))
    (hUorbit : RankOne.U K ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (hpair : ∀ g ∈ (T : Subgroup G), K.conjBy g = K ∨ K.conjBy g = L)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htout : t ∉ T₁) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G)) : False :=
  alternating_three_counterexample_false_of_g6 T hG
    (ChapterG.Section06.normalizedCubicSourceInput_knownSimple_of_earlier_classification hA h36 h4)
    H R K L T₁ hRT hTR h ha h' hKL hH hHe hcoreU hT₁ hhalf hNK hUorbit hpair
    t ht htout hKt x hx hxR hnc
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
