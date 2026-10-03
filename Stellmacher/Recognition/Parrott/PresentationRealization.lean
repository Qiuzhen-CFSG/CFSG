module

public import Stellmacher.Recognition.Parrott.BraidRelation
public import Stellmacher.Recognition.Parrott.AmbientGeneration

/-!
# Realization of Parrott's presentation

The original finite nonsolvable simple N₂-group and centralizer hypotheses
produce ten generators satisfying all 37 Parrott relators, with the prescribed
involution recovered as s₁s₅². These generators generate the ambient group.

The local construction supplies one compatible centralizer and normalizer
frame. The braid theorem proves VI(i) for this same frame, completing the
other 36 relators. The stronger existence theorem retains the second elementary
subgroup, normalizer, two involution classes, and second centralizer on these
same witnesses for the ambient-order argument.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§§2–4, pp.675–683, and the generator correspondence and VI(i) in §6, p.684.
-/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {z : G}

/-- The full presentation and ambient generation hold for one actual compatible
local configuration, retaining its fusion data and second centralizer. -/
public theorem parrott_presentation_realization_with_configuration
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∃ e : ParrottSecondElementaryData z, ∃ n : ParrottNormalizerFusionData e,
      ∃ f : ParrottCentralizerGeneratorData n, ∃ k : ParrottNormalizerGeneratorData f,
        ParrottSecondCentralizerData n ∧
        Tits.SatisfiesParrottRelations k.words ∧
        k.words .s1 * (k.words .s5) ^ 2 = z ∧
        Subgroup.closure (Set.range k.words) = ⊤ := by
  obtain ⟨e, n, ⟨⟨f, k⟩⟩⟩ := parrott_local_generators_exists hns hN h
  exact ⟨e, n, f, k, n.second_centralizer_data h hN,
    k.satisfiesParrottRelations h hN, k.anchor, k.closure_words_eq_top h hN⟩

/-- Parrott's ten generators satisfy all 37 relators, recover the original
involution, and generate the ambient group under the original hypotheses. -/
public theorem parrott_generating_presentation_realization
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∃ g : Tits.ParrottGenerator → G,
      Tits.SatisfiesParrottRelations g ∧
      g .s1 * (g .s5) ^ 2 = z ∧ Subgroup.closure (Set.range g) = ⊤ := by
  obtain ⟨_, _, _, k, _, hrels, hanchor, hgen⟩ :=
    parrott_presentation_realization_with_configuration hns hN h
  exact ⟨k.words, hrels, hanchor, hgen⟩

/-- The actual ten-generator realization of Parrott's presentation, with no
additional generator, fusion, centralizer, or recognition assumptions. -/
public theorem parrott_presentation_realization
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∃ g : Tits.ParrottGenerator → G,
      Tits.SatisfiesParrottRelations g ∧ g .s1 * (g .s5) ^ 2 = z := by
  obtain ⟨g, hrels, hanchor, _⟩ := parrott_generating_presentation_realization hns hN h
  exact ⟨g, hrels, hanchor⟩

end Stellmacher.Recognition
