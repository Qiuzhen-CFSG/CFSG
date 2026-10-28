module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.SourceInputs

/-!
# Constructing the literal maximal local omega-module

The witnessed component has a Sylow-normalized maximal local overcomponent.
Characteristic two makes its omega-span reduced, and the commutator with its
two-residual remains reduced and nonzero. Sylow averaging gives exactly the
source splitting with the fixed factor in the original omega-center.

The final theorem below applies the two explicitly retained earlier inputs
to this same overcomponent. It supplies the quotient list and the failure of
Baumann normalization; it does not yet prove LocalCartanFFReduction. The FF
classification, both Thompson equalities, irreducibility, cardinalities and
movement by the original residual remain with this module's assembly owner.

Source: Aschbacher--Smith 5.1.13, p.637, using 1.2.4, 1.2.8 and B.2.14.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The initial source construction, without a model or FF premise. -/
theorem localCartan_maximal_reduced_configuration
    {T : Sylow 2 G} {L W H A Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G,
      X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ¬ K ≤ omegaCentralizer T ∧
      localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)) ∧
      localOmegaModule T K ≠ ⊥ ∧
      conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K =
        localOmegaModule T K ⊔
          (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  obtain ⟨K,hK,hXK,hn,hC⟩ :=
    d.exists_normalized_maximal_local h.qtke hH.1.1.2 hY hXC
  exact ⟨K,hXK,hK,hn,hC,LocalOmega.module_reduced T K (h.qtke.evenCharacteristic T) hK.1 hn,
    LocalOmega.module_ne_bot T K hC,
    LocalOmega.span_eq T K (h.qtke.evenCharacteristic T) hK.1 hn⟩

/-- The two earlier inputs act on the same constructed K, without assuming an
A₇ quotient, irreducibility or any conclusion about the chosen module. -/
theorem localCartan_maximal_models_of_earlier_inputs
    (hmodels : ExceptionalLocalOvercomponentModels G)
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
          (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  obtain ⟨K,hXK,hK,hn,_,hU,hUne,hspan⟩ :=
    localCartan_maximal_reduced_configuration h hH hY d hXC
  refine ⟨K,hXK,hK,hn,?_,?_,hU,hUne,hspan⟩
  · exact hmodels h.qtke T X K (d.mem_localFamily hH.1.1.2 hY)
      (d.sylow_normalizes hH.1.1.2 hY.2) hK hXK d.component_model
  · intro hKB
    exact d.component_escape hH.1.1.2 h.sylow_normalizes hH.1.2
      (hXK.trans (hKB.trans (hbaum T L W n h)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
