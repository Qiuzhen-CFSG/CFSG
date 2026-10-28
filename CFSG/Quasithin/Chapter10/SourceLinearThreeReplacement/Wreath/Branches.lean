module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Contracts
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# The two remaining source branches of 10.3.3

These are outstanding source obligations, not recognition theorems. The
Bender branch asks for the actual quotient isomorphism and the original
component orbit. The complementary branch asks for the source's generation
by a set of parameter-one minimal parabolics; its contradiction is proved
in `Wreath.Assembly`. In particular it need not classify every parabolic.

Source: Aschbacher--Smith 10.3.3, printed p.756, using 10.2.3(3) and 10.2.4,
printed pp.744--747.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- The Bender-component branch, with literal quotients and subgroup embeddings. -/
def BenderRecognitionAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s)
    (I : Subgroup G),
    I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)) →
    ¬ I ≤ D.maximalLocal → ClassificationModels.IsBenderModel (I ⧸ pCore 2 I) →
    Nonempty ((componentJoin T L (d.first * d.second) ⧸
      pCore 2 (componentJoin T L (d.first * d.second))) ≃*
      Theory.SpecificGroups.SymmetricFive.WreathComponents.W) ∧
    componentOrbit I (T : Subgroup G) = componentSpan T L (d.first * d.second)

/-- The non-Bender branch returns an actual escaping component and the
minimal-parabolic generating family that contradicts the weak-closure bound. -/
def NonBenderGenerationAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s),
    (∀ I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)),
      ¬ I ≤ D.maximalLocal → ¬ ClassificationModels.IsBenderModel (I ⧸ pCore 2 I)) →
    ∃ I : Subgroup G,
      I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)) ∧
      ¬ I ≤ D.maximalLocal ∧
      let Y := componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G)
      let S : Sylow 2 Y := T.subtype le_sup_right
      ∃ Δ : Set (Subgroup Y),
        (∀ P ∈ Δ, ChapterB.IsMinimalParabolicOver S P ∧ ChapterE.generationParameter P = 1) ∧
        sSup Δ ⊔ normalizer (S : Set Y) = ⊤

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
