module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SectionSource
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source
/-!
# E.6.3 with the original block source discharged

The full known-simple E.6.7 producer supplies its unchanged decomposition
contract. SourceSelection then constructs the actual E.6.11 section used by
E.6.24–25. No block-family, Borel-marking, torus-regularity, normal-image or
selected-section premise remains in this lower-bound application.

The earlier component sieve, hyperplane bound, global odd-core conclusion,
genuine A.3.12 embedding statement, and regular-cyclic factor-seed theorem
remain with their source producers.
Source: Aschbacher–Smith, E.6.3, E.6.7, E.6.11 and E.6.23–25.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open Components LocalFactors Hyperplanes.ComponentBalance Hyperplanes.Enlargement
open InvariantSubspaces.BlockSelection Representation.RegularCyclicNormalClosure
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

/-- Supply the complete original E.6.7 theorem in the literal E.6.3 consumer. -/
theorem lower_bound_knownSimple_of_component_sources [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
    (ho : OddCoreFree V)
    (h68 : ∀ U ∈ obstructionFamily M V, ∀ L : Subgroup G,
      ComponentIn (centralizer (U : Set G)) L →
        (∃ n, BorelAlternative M V U L n) ∨
          (∃ n, SymplecticAlternative M V U L n) ∨ globalR V = 1)
    (h23 : 1 < globalR V)
    (hONan : ∀ X : Subgroup G,
      Input (automizerRepresentation V) (inducedAutomizer V X) →
        ∃ B : Subgroup (Automizer V),
          FactorSeed (automizerRepresentation V) (inducedAutomizer V X) B) :
    (localM V : ℕ∞) ≤ globalR V ∧
      globalS V = (localM V : ℕ∞) ∧ 2 < globalS V := by
  exact lower_bound_knownSimple_of_source_sections h hm hA312 ho (e67Input_knownSimple h)
    h68 h23 hONan
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
