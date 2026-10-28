module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Classification

/-!
# The complete faithful-component sieve at the original G,T

Reselect each faithful component in the same counterexample before applying
13.3.16 or 13.8.1. The unitary quotient cannot be A₅ by its order. Both
ordinary and covered A₆ quotients give the literal quotient by centralCore;
its recognition contradicts the original Sp₆(2)/U₄(3) exclusions. The earlier
five-model list therefore leaves exactly A₅ and L₃(2), with relative normality
in CT and maximality in the whole local family supplied by local rigidity.

All earlier implications are confined to this G,T. No universal source record
is constructed. The genuine Source1332OneTwo, unitary and six-letter source
proofs remain with qt-d-1332-source, qt-d-13316-source and qt-d-1381-source;
this conditional family supplies their literal Chapter14 consumers.

Source: Aschbacher–Smith, 13.3.1–2, pp.884–885; 13.3.16, p.894;
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

/-- The earlier unitary implication for every reselected component at the
original G,T, retaining every clause of Hypothesis 13.3.1. -/
def Theorem13316At (T : Sylow 2 G) : Prop :=
  ∀ C : Subgroup G, Hypothesis1331 T C →
    ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3

/-- The full ordinary and covered six-letter recognition implication at the
original G,T, on the literal quotient by the preimage of the covering center. -/
def Theorem1381At (T : Sylow 2 G) : Prop :=
  ∀ C : Subgroup G, Hypothesis1331 T C →
    Nonempty ((C ⧸ centralCore C) ≃* alternatingGroup (Fin 6)) →
    ClassicalGroup.IsPSp G 3 2 ∨ ClassicalGroup.IsPSU G 4 3

/-- Apply the genuine earlier recognition theorem to an arbitrary original
faithful component, using the proved reselection rather than a new FSU premise. -/
theorem not_A6_centralQuotient_of_source_at
    {T : Sylow 2 G} {L : Subgroup G} (d : Counterexample T L)
    (source1381 : Theorem1381At T) (C : Subgroup G)
    (hC : C ∈ Chapter1.L G (T : Subgroup G)) (hf : IsFaithfulSignalizerType C) :
    ¬ Nonempty ((C ⧸ centralCore C) ≃* alternatingGroup (Fin 6)) := by
  intro hsix
  have dC : Counterexample T C := reselect_A6 d hC hf hsix
  rcases source1381 C (hypothesis1331 dC) hsix with hsp | hsu
  · exact d.no_symplectic_six hsp
  · exact d.no_unitary_four hsu

/-- The ordinary A₆ alternative of 13.5.2 is excluded using its actual
center-free core quotient, without confusing it with the triple-cover branch. -/
theorem not_A6_coreQuotient_of_source_at
    {T : Sylow 2 G} {L : Subgroup G} (d : Counterexample T L)
    (source1381 : Theorem1381At T) (C : Subgroup G)
    (hC : C ∈ Chapter1.L G (T : Subgroup G)) (hf : IsFaithfulSignalizerType C) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 6)) :=
  fun hsix => not_A6_centralQuotient_of_source_at d source1381 C hC hf
    (A6_centralQuotient_of_coreQuotient C hsix)

/-- The same consumer excludes a supplied actual central cover of A₆ on
C/O₂(C). The kernel comparison is literal; no abstract cover tag is used. -/
theorem not_central_cover_A6_of_source_at
    {T : Sylow 2 G} {L : Subgroup G} (d : Counterexample T L)
    (source1381 : Theorem1381At T) (C : Subgroup G)
    (hC : C ∈ Chapter1.L G (T : Subgroup G)) (hf : IsFaithfulSignalizerType C)
    (f : (C ⧸ pCore 2 C) →* alternatingGroup (Fin 6))
    (hsurj : Function.Surjective f) (hk : f.ker = center (C ⧸ pCore 2 C)) : False :=
  not_A6_centralQuotient_of_source_at d source1381 C hC hf
    ⟨centralQuotient_equiv_of_cover C f hsurj hk⟩


/-- Reselect the literal unitary component before using 13.3.16. -/
theorem not_unitary_coreQuotient_of_source_at (d : Counterexample T L)
    (source13316 : Theorem13316At T)
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
  exact source13316 C (hypothesis1331 (reselect d hC hf hne)) hu

/-- Both central-cover maps are retained when eliminating the triple A₆ row. -/
theorem not_A6_cover_coreQuotient_of_source_at (d : Counterexample T L)
    (source1381 : Theorem1381At T)
    (hC : C ∈ Chapter1.L G (T : Subgroup G)) (hf : IsFaithfulSignalizerType C) :
    ¬ IsAlternatingCover (C ⧸ pCore 2 C) 6 := by
  rintro ⟨_, _, ⟨e⟩⟩
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center (C ⧸ pCore 2 C)))
  apply not_central_cover_A6_of_source_at d source1381 C hC hf f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  ext x
  change e (QuotientGroup.mk' (center (C ⧸ pCore 2 C)) x) = 1 ↔
    x ∈ center (C ⧸ pCore 2 C)
  rw [map_eq_one_iff e e.injective]
  exact QuotientGroup.eq_one_iff x

/-- The exact earlier classification consumed by the later Rudvalis
component selections. No module, normality or maximality conclusion is assumed. -/
theorem earlierFaithfulClassification_of_sources_at (d : Counterexample T L)
    (source1332 : Source1332OneTwo T) (source13316 : Theorem13316At T)
    (source1381 : Theorem1381At T) : EarlierFaithfulClassification G (T : Subgroup G) := by
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
  · exact (not_A6_coreQuotient_of_source_at d source1381 C hC hf h6).elim
  · exact (not_A6_cover_coreQuotient_of_source_at d source1381 hC hf hc6).elim
  · exact (not_unitary_coreQuotient_of_source_at d source13316 hC hf hu).elim

/-- The actual 14.4.8 selection application with its faithful-classification
premise discharged by the source sieve, retaining the original action map. -/
theorem selectedComponent_of_sources_at (d : Counterexample T L)
    (source1332 : Source1332OneTwo T) (source13316 : Theorem13316At T)
    (source1381 : Theorem1381At T) (earlier : EarlierComponentGeneration G)
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
    (earlierFaithfulClassification_of_sources_at d source1332 source13316 source1381)
    hX hV₂T hTL₂ hn hs


end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
