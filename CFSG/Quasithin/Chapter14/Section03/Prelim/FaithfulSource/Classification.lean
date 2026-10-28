module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource
public import CFSG.Quasithin.Chapter13.Section03.SourceComponentRigidity
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.StarPlacement
public import CFSG.Quasithin.Chapter1.Section02.Adequate.OrbitFaithful
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction.Components.Selection

/-!
# The faithful-component sieve in the D case of 14.3.4

The earlier five-model list applies to every faithful local component.
Faithfulness ascends to any containing local component; the solvable proper
Sylow-overgroup property of the five models then proves maximality. The
earlier T-normalization gives normality in the literal join with T.

Reselection preserves the original counterexample for the unitary row,
because its order excludes A₅. The genuine 13.3.16 implication eliminates
that row. The original 13.8.1 implication eliminates both A₆ rows through
the literal central quotient, including the triple cover. The surviving
binary linear model is transported to the exact carrier used by the
14.4.8 component-selection consumer.

This is a conditional assembly, not an assertion of the earlier sources.
The inputs are owned by qt-d-1332-source, qt-d-13316-source and
qt-d-1381-source. The natural-module clause additionally needs the original
12.4.2 exclusion and is not asserted here.

Source: Aschbacher–Smith, 13.3.2(1–2,5), pp.884–885; 13.3.16, p.894;
13.8.1, p.946; 14.3.4(1–2), p.990, and 14.4.8(2), p.1009.
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter1.Section02.LocalModels ChapterA.Section04
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L C : Subgroup G}

/-- The universal core-quotient exclusion supplied by the original unitary
source theorem, after its faithful-action comparison. -/
def Theorem13316 : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X) (A : Subgroup X),
    Hypothesis1331 S A → ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3

/-- The earlier list and T-normality already imply maximality in the full
local family, including overgroups not initially assumed faithful. -/
theorem normal_maximal_of_source1332 (d : Counterexample T L)
    (source1332 : Source1332OneTwo T)
    (hC : C ∈ Chapter1.L G (T : Subgroup G)) (hf : IsFaithfulSignalizerType C) :
    (C.subgroupOf (C ⊔ (T : Subgroup G))).Normal ∧
      C ∈ Chapter1.LStar G (T : Subgroup G) := by
  have hc := (faithfulLocalComponents_iff C).mpr ⟨hC, hf⟩
  have hn := (source1332 C hc).1
  refine ⟨(normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le C.le_normalizer hn), hC, ?_⟩
  intro I hI hCI
  have hi := Chapter1.Section02.Adequate.faithful_local_overgroup T
    (d.qtke.evenCharacteristic T) hc hI hCI
  exact (local_eq_of_midSize hI hC hCI (source1332 I hi).2).symm

/-- Reselect the literal unitary component before using 13.3.16. -/
theorem not_unitary_coreQuotient_of_source (d : Counterexample T L)
    (source13316 : Theorem13316.{u})
    (hC : C ∈ Chapter1.L G (T : Subgroup G)) (hf : IsFaithfulSignalizerType C) :
    ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3 := by
  intro hu
  have hne : ¬ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) := by
    rintro ⟨e5⟩
    obtain ⟨F, _, _, J, hF, hJ, ⟨e⟩⟩ := hu
    have hc := (Nat.card_congr e.toEquiv).trans
      (BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.card_projective J hF hJ)
    rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup] at hc
    norm_num at hc
  exact source13316 G T C (hypothesis1331 (reselect d hC hf hne)) hu

/-- Both central-cover maps are retained when eliminating the triple A₆ row. -/
theorem not_A6_cover_coreQuotient_of_source (d : Counterexample T L)
    (source1381 : Theorem1381.{u})
    (hC : C ∈ Chapter1.L G (T : Subgroup G)) (hf : IsFaithfulSignalizerType C) :
    ¬ IsAlternatingCover (C ⧸ pCore 2 C) 6 := by
  rintro ⟨_, _, ⟨e⟩⟩
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center (C ⧸ pCore 2 C)))
  apply not_central_cover_A6_of_source d source1381 C hC hf f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  ext x
  change e (QuotientGroup.mk' (center (C ⧸ pCore 2 C)) x) = 1 ↔
    x ∈ center (C ⧸ pCore 2 C)
  rw [map_eq_one_iff e e.injective]
  exact QuotientGroup.eq_one_iff x

/-- The exact earlier classification consumed by the later Rudvalis
component selections. No module, normality or maximality conclusion is assumed. -/
theorem earlierFaithfulClassification_of_sources (d : Counterexample T L)
    (source1332 : Source1332OneTwo T) (source13316 : Theorem13316.{u})
    (source1381 : Theorem1381.{u}) : EarlierFaithfulClassification G (T : Subgroup G) := by
  intro C hC hf
  have hn := normal_maximal_of_source1332 d source1332 hC hf
  refine ⟨?_, hn⟩
  have hm := (source1332 C ((faithfulLocalComponents_iff C).mpr ⟨hC, hf⟩)).2
  rcases hm with h5 | h3 | h6 | hc6 | hu
  · exact .inl h5
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h3
    let := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
    exact .inr ⟨e.trans (Atlas.fieldEquivPSL 3 eF)⟩
  · exact (not_A6_coreQuotient_of_source d source1381 C hC hf h6).elim
  · exact (not_A6_cover_coreQuotient_of_source d source1381 hC hf hc6).elim
  · exact (not_unitary_coreQuotient_of_source d source13316 hC hf hu).elim

/-- The actual 14.4.8 selection application with its faithful-classification
premise discharged by the source sieve, retaining the original action map. -/
theorem selectedComponent_of_sources (d : Counterexample T L)
    (source1332 : Source1332OneTwo T) (source13316 : Theorem13316.{u})
    (source1381 : Theorem1381.{u}) (earlier : EarlierComponentGeneration G)
    {H V₂ E X L₂ : Subgroup G}
    (hX : X ∈ Chapter14.Section04.LargerDimension.YFamily H T V₂ E)
    [IsElementaryAbelian 2 (Chapter14.Section04.LargerDimension.movedSpace V₂ X)]
    (hV₂T : V₂ ≤ T) (hTL₂ : (T : Subgroup G) ≤ normalizer (L₂ : Set G))
    (hn : Chapter14.Section04.LargerDimension.localJoin L₂ X ⊔ (T : Subgroup G) ≤
      normalizer (Chapter14.Section04.LargerDimension.movedSpace V₂ X : Set G))
    (hs : Function.Surjective (Chapter14.Section04.LargerDimension.LocalAction.conjugation
      (Chapter14.Section04.LargerDimension.localJoin L₂ X)
      (Chapter14.Section04.LargerDimension.movedSpace V₂ X) (le_sup_left.trans hn))) :
    Nonempty (SelectedComponent (Chapter14.Section04.LargerDimension.localJoin L₂ X)
      (Chapter14.Section04.LargerDimension.movedSpace V₂ X) T (le_sup_left.trans hn)) :=
  exists_selectedComponent_of_Y earlier T (d.qtke.evenCharacteristic T)
    (earlierFaithfulClassification_of_sources d source1332 source13316 source1381)
    hX hV₂T hTL₂ hn hs

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
