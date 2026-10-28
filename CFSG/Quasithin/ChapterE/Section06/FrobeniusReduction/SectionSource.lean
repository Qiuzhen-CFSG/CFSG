module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.KnownSimpleSource
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceSelection

/-!
# E.6.3 with the original E.6.11 section constructed

SourceSelection constructs the selected component or block and its actual
torus directly at the full globalR minimum. The literal E.6.24–25 consumer
therefore no longer assumes any selected regular section. Both Chapter 1.2
inputs are already discharged, and the genuine full A.3.12 input still supplies
the original 3.1.1 common-normal statement.

The remaining earlier-source obligations are E.6.7, the component sieve E.6.8,
the hyperplane bound and global odd-core conclusion E.6.21–23, and the cited
regular-cyclic normal-closure seed. These are explicitly retained, rather
than replaced by assumed factorization or exclusion conclusions.
Source: Aschbacher–Smith, E.6.3 and E.6.11, E.6.23–25, pp.245,249–250,255–256.
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

/-- Supply the original E.6.11 section in the actual lower-bound consumer. -/
theorem lower_bound_knownSimple_of_source_sections [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
    (ho : OddCoreFree V) (h67 : E67Input T M V)
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
  apply lower_bound_knownSimple_of_earlier_sources h hm hA312 ho h67 ?_ h23 ?_ hONan
  · intro U hU L hL
    rcases h68 U hU L hL with hb | hs | he
    · exact Or.inl hb
    · exact Or.inr (Or.inl hs)
    · exact (h23.ne' he).elim
  · intro U hU hmin hr
    exact minimalRegularSection_of_source_models h h67 hU hmin hr (h68 U hU)
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
