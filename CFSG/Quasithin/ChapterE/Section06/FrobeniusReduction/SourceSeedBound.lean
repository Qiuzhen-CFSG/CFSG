module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceBound
public import CFSG.Quasithin.RegularCyclicNormalClosure.FactorConstruction.SourceAssembly
/-!
# The original E.6.3 consumer with regular-cyclic factor existence discharged

The complete regular-cyclic source constructs a factor seed for the literal
representation of the original automizer on V and its induced cyclic subgroup.
SourceBound applies it only to the actual section selected at the full global
minimum. This eliminates the O’Nan seed callback without changing any actor,
quotient, fixed subspace, minimum domain or source embedding hypothesis.

Only the full genuine A.3.12 theorem and the remaining component-model sources
E.6.8, E.6.18 and the further E.6.23 recognition are explicit.
Source: Aschbacher–Smith E.6.3 and E.6.24–25, pp.245,255–256; Aschbacher
(1981), Weak closure in finite groups of even characteristic, Theorem10.4.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open Components Hyperplanes Hyperplanes.ComponentBalance Hyperplanes.Enlargement
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

theorem lower_bound_knownSimple_of_component_models [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
    (h18 : SevenExcluded M V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X)
    (hquot : SixAutomorphisms.ModelIdentification.QuotientRecognition T M V) :
    (localM V : ℕ∞) ≤ globalR V ∧
      globalS V = (localM V : ℕ∞) ∧ 2 < globalS V := by
  exact lower_bound_knownSimple_of_source_models h hm hA312 h18 h68 hquot
    (fun _ hi => CFSG.Quasithin.RegularCyclicNormalClosure.exists_factorSeed_of_input hi)
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
