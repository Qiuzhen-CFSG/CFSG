module

public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.MaximalReduction
public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.LinearThreeNatural
public import CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource.Classification
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBaumannSource

/-!
# The literal 13.3.2 inputs for the later source consumers

The maximal-component reduction is applied to each original faithful K,
without reselecting the distinguished component of Hypothesis 13.3.1.
For A₅, the natural central quotient of the original Irr⁺ space lifts to
the entire original subgroup by projectivity and commutator generation.
For L₃(2), the order-eight conclusion determines the faithful natural action.
These constructions supply exactly the public Chapter 13 and 14 inputs.

This is conditional source assembly. The maximal quasisimplicity, refined
maximal quotient catalogue, A₅ central-quotient classification and L₃(2)
order-eight assertion remain explicit earlier mathematical obligations.
The last assertion requires the 12.4.2 indecomposable exclusion as well as
the seven-case theorem. None is claimed to follow from Structural1222.

Source: Aschbacher--Smith, 12.2.2(3a,b,d), 12.4.2, 13.1.2(3), 13.1.7,
and 13.3.2(1--4), printed pp.795,812,866,870,884--885.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceClassification
open Chapter12.Section02 Chapter13.Section01
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Noncentrality.SupercriticalSource
universe u

variable
  (quasisimple : ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X),
    Hypothesis1311 S → ∀ I : Subgroup X, FaithfulMaximalLocal S I →
      IsQuasisimple (I ⧸ pCore 2 I))
  (models : ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X),
    Hypothesis1311 S → ∀ I : Subgroup X,
      Hypothesis1223 KnownSimple.IsKnownSimple S I → MidSizeModel (Chapter1.XiQuotient I))

include quasisimple models

/-- The universal A₅ input for the plane-centralizer and Rudvalis consumers,
from the earlier natural central-quotient classification on maximal members. -/
theorem alternatingFiveModules1332_of_maximal_sources
    (natural : ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X) (I : Subgroup X),
      Hypothesis1223 KnownSimple.IsKnownSimple S I →
      Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 5)) →
      ∀ (W : Subgroup X) (D : ChosenModule S I W),
        ∃ (e : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 5))
          (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5)),
          ∀ (i : I) v, a (D.chosenCentralAction i v) =
            Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 I) i)) (a v)) :
    PlaneNoncentralitySource.AlternatingFiveModules1332.{u} := by
  intro G _ _ T L d K hK hfive V D
  have h := Chapter14.Section03.FaithfulSource.Counterexample.hypothesis1311 d
  obtain ⟨hk, _⟩ := faithful_hypothesis1223_of_maximal_models h
    (quasisimple G T h) (models G T h) hK
  obtain ⟨e, a, ha⟩ := natural G T K hk hfive V D
  exact D.a5_model_of_central_quotient e a ha

/-- The exact 14.3 case-one input, retaining the original chosen V and
original quotient projection. Only its order-eight source remains to be supplied. -/
theorem earlier1332CaseOne_of_maximal_sources
    (card : ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X) (I : Subgroup X),
      Hypothesis1311 S → Hypothesis1223 KnownSimple.IsKnownSimple S I →
      ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 3 2 →
      ∀ (W : Subgroup X), ChosenModule S I W → Nat.card W = 8) :
    Chapter14.Section03.CaseOneSource.Earlier1332CaseOne.{u} := by
  intro G _ _ T L d hq
  have h := Chapter14.Section03.FaithfulSource.Counterexample.hypothesis1311 d
  obtain ⟨hl, _⟩ := faithful_hypothesis1223_of_maximal_models h
    (quasisimple G T h) (models G T h) d.local_component
  exact ⟨hl.maximal_faithful, hl.quasisimple,
    fun V D => linearThree_marking_of_card D hq (card G T L h hl hq V D)⟩

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The same distinguished member is maximal among the actual Chapter 14
counterexamples. No replacement of L or its chosen module is made. -/
theorem counterexample_maximal_of_maximal_sources (d : Counterexample T L) :
    Maximal (Counterexample T) L := by
  have h := Chapter14.Section03.FaithfulSource.Counterexample.hypothesis1311 d
  obtain ⟨hl, _⟩ := faithful_hypothesis1223_of_maximal_models h
    (quasisimple G T h) (models G T h) d.local_component
  refine ⟨d, ?_⟩
  intro I hi hLI
  exact (hl.maximal_faithful.1.2 I
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T I).mp
      hi.local_component).1 hLI).le

/-- The actual ordinary Baumann consumer now obtains selected-member
maximality and the full faithful-family catalogue from the earlier sources. -/
theorem ordinary_six_full_span_abelian_of_maximal_sources
    {V V₁ V₂ V₃ M G₁ : Subgroup G}
    (d : Chapter13.Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2, V₂⁆ ≠ ⊥)
    (modules : PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    IsMulCommutative (conjugateSpanBy V G₁) := by
  have h := Chapter14.Section03.FaithfulSource.Counterexample.hypothesis1311 d.counterexample
  exact Chapter14.Section08.LieTypeBranch.original_six_full_span_abelian d
    (counterexample_maximal_of_maximal_sources quasisimple models d.counterexample) eL hm
    (source1332OneTwo_of_maximal_models h
      (quasisimple G T h) (models G T h) structural) modules

/-- The original starred-family placement consumer, with 13.3.2(1--2)
assembled on its literal faithful family from the earlier maximal sources. -/
theorem source_XiF_subset_XiStarF_of_maximal_sources
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Chapter1.XiF G (T : Subgroup G) ⊆ Chapter1.XiStarF G (T : Subgroup G) := by
  have hs := h.hypothesis1311
  exact source_XiF_subset_XiStarF h.qtke T
    (source1332OneTwo_of_maximal_models hs
      (quasisimple G T hs) (models G T hs) structural)

end CFSG.Quasithin.Chapter13.Section03.SourceClassification
