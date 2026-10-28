module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsJankoFourInput
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction

/-!
# The original Mathieu branch of the maximal local Cartan construction

The actual M₂₃ local section survives enlargement by the proved two-local
placement in J₄. Apply that theorem to the same maximal local component K
provided by the Cartan construction. This removes the arbitrary maximal
Sylow-overgroup catalogue from this source branch; the independent earlier
Baumann normalizer theorem remains explicit.

The A₇ branch and the full exceptional-overcomponent assembly remain separate
source obligations. Existing conditional public theorems are unchanged.

Source: Aschbacher–Smith 1.2.8, pp.506–507, and 5.1.13, p.637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original M₂₃ Cartan branch needs only the independently owned Baumann
normalizer theorem, with no additional J₄ classification premise. -/
theorem localCartan_maximal_models_of_mathieuTwentyThree_source
    (hbaum : RankOneBaumannNormalizerControl G)
    {T : Sylow 2 G} {L W H A Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T)
    (hM : Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M23)) :
    ∃ K : Subgroup G,
      X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      LocalExceptionalQuotient K ∧
      ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)) ∧
      localOmegaModule T K ≠ ⊥ ∧
      conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K =
        localOmegaModule T K ⊔
          (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  obtain ⟨K, hXK, hK, hn, _, hU, hUne, hspan⟩ :=
    localCartan_maximal_reduced_configuration h hH hY d hXC
  have hm :=
    Chapter1.Section02.ExceptionalOvercomponents.mathieuTwentyThree_local_overcomponent
      h.qtke T (d.mem_localFamily hH.1.1.2 hY)
      (d.sylow_normalizes hH.1.1.2 hY.2) hK.1 hXK hM
  refine ⟨K, hXK, hK, hn, Or.inr (Or.inr hm), ?_, hU, hUne, hspan⟩
  intro hKB
  exact d.component_escape hH.1.1.2 h.sylow_normalizes hH.1.2
    (hXK.trans (hKB.trans (hbaum T L W n h)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
