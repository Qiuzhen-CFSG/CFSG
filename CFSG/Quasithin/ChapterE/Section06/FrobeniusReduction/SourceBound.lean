module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.BlockSource
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SourceEnlargement
/-!
# The original E.6.3 lower bound from the remaining source model producers

E.6.19–22 construct odd-core vanishing and characteristic-two hyperplane
centralizers. The original E.6.23 block argument now proves r > 1, with only
its exact further-component recognition left to the model owner. Complete E.6.7
and the selected minimum construction then feed E.6.24–25 on the original
actor and on the full domain of globalR, including the trivial subgroup.

The remaining hypotheses are the genuine full A.3.12 embedding theorem,
the E.6.8 sieve, E.6.18 exclusion, E.6.23 quotient recognition, and the actual
regular-cyclic factor-seed theorem. No odd-core conclusion, hyperplane bound,
block selection, regular-section witness, orbit-model or I.3 premise remains.
Source: Aschbacher–Smith, E.6.3 and E.6.18–25, pp.245,252–256.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open Components Hyperplanes Hyperplanes.ComponentBalance Hyperplanes.Enlargement
open Representation.RegularCyclicNormalClosure
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

theorem lower_bound_knownSimple_of_source_models [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
    (h18 : SevenExcluded M V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X)
    (hquot : SixAutomorphisms.ModelIdentification.QuotientRecognition T M V)
    (hONan : ∀ X : Subgroup G,
      Input (automizerRepresentation V) (inducedAutomizer V X) →
        ∃ B : Subgroup (Automizer V),
          FactorSeed (automizerRepresentation V) (inducedAutomizer V X) B) :
    (localM V : ℕ∞) ≤ globalR V ∧
      globalS V = (localM V : ℕ∞) ∧ 2 < globalS V := by
  have h311 := InvariantSubspaces.source_commonNormalInput_of_A312 T hA312
  exact lower_bound_knownSimple_of_component_sources h hm hA312
    (source_oddCoreFree h (Or.inr hm) h311 h18 h68)
    (fun A hA X hX => (h68 A hA X hX).borel_symplectic_or_rank_one)
    (source_rank_gt_one_of_quotientRecognition h hm h311 h18 h68 hquot) hONan
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
