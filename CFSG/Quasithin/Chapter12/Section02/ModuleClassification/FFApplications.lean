module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CorrectedCatalogue
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.SeedNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.ExtensionComparison

/-!
# B.5 source applications on the original chosen module

The actual seed and full-normalizer offender conclusions are transported to
the seven original alternatives. The rank-one and nonbinary source exits
remain explicit; the source orbit branch supplies T-invariance where needed.
Source: Aschbacher--Smith B.5.1 and 12.2.2, pp.99--103 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- Apply the complete source classification to the literal full-normalizer
offender supplement, then compare every row on the unchanged chosen space. -/
theorem alternatives_of_fullNormalizer_source_exits_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (horbits : componentOrbit V (normalizer (L : Set G)) = V ∨
      (componentOrbit V (T : Subgroup G) = V ∧ V ⊓ centralizer (L : Set G) = ⊥))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction))
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False) : ModuleAlternatives1222 D := by
  have hff' : IsFFModule (normalizerRepresentation D.seedComponentAction) :=
    D.chosen_normalizer_ff_iff_seedComponent.mp hff
  obtain ⟨A,hA,hK,⟨b⟩⟩ := D.full_normalizer_source_conclusion h.toHypothesis1221 hff'
  let : Finite (supplement (D.seedRepresentation.comp D.componentImage.subtype) A) :=
    supplement_finite _ A
  exact (D.normalizerOffenderComparison A hK).alternatives_of_corrected_source_exits_of_many
    h hmany horbits hff hrank hnonbinary b

/-- The actual seed-actor FF witness has the same row comparison. No
identification of the seed with its Sylow orbit is inferred from FF alone. -/
theorem alternatives_of_seed_source_exits_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (horbits : componentOrbit V (normalizer (L : Set G)) = V ∨
      (componentOrbit V (T : Subgroup G) = V ∧ V ⊓ centralizer (L : Set G) = ⊥))
    (hseed : IsFFModule D.seedRepresentation)
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False) : ModuleAlternatives1222 D := by
  obtain ⟨hK,⟨b⟩⟩ := D.seed_quasisimple_source_conclusion h.toHypothesis1221 hseed
  exact (D.seedOffenderComparison hK).alternatives_of_corrected_source_exits_of_many
    h hmany horbits (D.chosen_normalizer_ff_of_seed hseed) hrank hnonbinary b

/-- The genuine 3.2.5 alternatives, after excluding their marked doubled
case, supply the orbit equalities used by the full-normalizer application. -/
theorem alternatives_of_source325_and_FF_exits_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h325 : D.Source325Alternatives) (hdoubled : ¬ D.MarkedDoubled)
    (hff : IsFFModule (normalizerRepresentation D.chosenAction))
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False) : ModuleAlternatives1222 D := by
  apply D.alternatives_of_fullNormalizer_source_exits_of_many h hmany _ hff hrank hnonbinary
  rcases h325 with ⟨_,hU⟩ | ⟨hW,hC,_⟩ | hd
  · exact Or.inl hU
  · exact Or.inr ⟨hW,hC⟩
  · exact (hdoubled hd).elim

/-- Clause two of the actual full-normalizer supplement on the original
relative-centralizer quotient, including nonzero central fixed space. -/
theorem nonsplitNatural_of_fullNormalizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hff : IsFFModule (normalizerRepresentation D.chosenAction))
    (hn : D.chosenAction.invariants ≠ ⊥) :
    letI := D.actionCentralizer_normal
    ChapterB.QuasisimpleSource.NonsplitNatural D.faithfulCentralAction := by
  have hff' : IsFFModule (normalizerRepresentation D.seedComponentAction) :=
    D.chosen_normalizer_ff_iff_seedComponent.mp hff
  obtain ⟨A,hA,hK,⟨b⟩⟩ := D.full_normalizer_source_conclusion h hff'
  exact (D.normalizerOffenderComparison A hK).corrected_clause_two b hn

/-- Clause two of the actual seed-actor source conclusion uses the same
canonical quotient marking; no orbit equality is needed for this transport. -/
theorem nonsplitNatural_of_seed
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hseed : IsFFModule D.seedRepresentation)
    (hn : D.chosenAction.invariants ≠ ⊥) :
    letI := D.actionCentralizer_normal
    ChapterB.QuasisimpleSource.NonsplitNatural D.faithfulCentralAction := by
  obtain ⟨hK,⟨b⟩⟩ := D.seed_quasisimple_source_conclusion h hseed
  exact (D.seedOffenderComparison hK).corrected_clause_two b hn

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
