module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponents
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenCatalogue
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.ExceptionalMathieuSource
/-!
# The complete exceptional local-overcomponent theorem for the Cartan construction

The original A₇, J₂ and M₂₃ quotient branches all preserve the exceptional
quotient list on the same maximal local overcomponent. The A₇ branch uses
the complete simple-carrier and genuine three-cover inspection; J₂ and M₂₃
use their established original local-overcomponent theorems. Every map is
through the literal intrinsic two-core quotient, with the original full
Sylow normalization and QTKE assumptions.

The actual Cartan construction now needs only the independent earlier
Baumann normalizer theorem. Its producer is
`qt-d-1222-local-cartan-ff-source-classification`; no exceptional embedding
or J₄ placement premise remains in the consumer below.
Source: Aschbacher–Smith 1.2.8, pp.506–507, and 5.1.13, p.637.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full original exceptional-overcomponent input is now proved over
the complete known-simple catalogue, with genuine covers retained. -/
theorem exceptionalLocalOvercomponentModels_source : ExceptionalLocalOvercomponentModels G := by
  intro hG T X K hX hn hK hXK hmodel
  rcases hmodel with hA|hJ|hM
  · exact Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenCatalogue.alternatingSeven_local_overcomponent
      hG T hX hn hK.1 hXK hA
  · have he := Chapter1.Section02.eq_of_jankoTwo_local_overcomponent
      hG T hX hn hK.1 hXK hJ
    exact Or.inr (Or.inl (he ▸ hJ))
  · exact Or.inr (Or.inr
      (Chapter1.Section02.ExceptionalOvercomponents.mathieuTwentyThree_local_overcomponent
        hG T hX hn hK.1 hXK hM))

/-- The literal maximal local Cartan configuration, with the full exceptional
model input discharged. Only the independent earlier Baumann theorem remains. -/
theorem localCartan_maximal_models_source
    (hbaum : RankOneBaumannNormalizerControl G)
    {T : Sylow 2 G} {L W H A Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G,
      X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      LocalExceptionalQuotient K ∧
      ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)) ∧
      localOmegaModule T K ≠ ⊥ ∧
      conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K =
        localOmegaModule T K ⊔
          (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) :=
  localCartan_maximal_models_of_earlier_inputs exceptionalLocalOvercomponentModels_source
    hbaum h hH hY d hXC

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
