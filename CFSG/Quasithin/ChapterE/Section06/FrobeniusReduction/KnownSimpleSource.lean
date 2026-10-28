module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceInputs
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.CommonNormalSource

/-!
# The known-simple E.6.3 assembly with Chapter 1 inputs discharged

The actual 1.2.4 containment and 1.2.1(3) residual-normalization inputs
are proved in SourceInputs. The original 3.1.1 producer supplies E.6.13
from its genuine full A.3.12 embedding hypothesis. The earlier E.6 local
structure, hyperplane bound, regular-section selection and O’Nan seed
existence remain with their source producers.

The conclusion is the original lower bound on the full globalR domain;
this conditional assembly does not claim those earlier results.
Source: Aschbacher–Smith, E.6.3 and E.6.25, printed pp.245,255–256.
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

/-- Supply the actual known-simple Chapter 1 and common-normal producers. -/
theorem lower_bound_knownSimple_of_earlier_sources [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
    (ho : OddCoreFree V) (h67 : E67Input T M V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ J : Subgroup G,
      CentralizerComponent A J →
        (∃ n, BorelAlternative M V A J n) ∨
        (∃ n, SymplecticAlternative M V A J n) ∨ actionCorank V J ≤ 2)
    (h23 : 1 < globalR V)
    (h11 : ∀ U ∈ obstructionFamily M V,
      (subgroupCorank V U : ℕ∞) = globalR V → 1 < subgroupCorank V U →
        Nonempty (MinimalRegularSection T M V U))
    (hONan : ∀ X : Subgroup G,
      Input (automizerRepresentation V) (inducedAutomizer V X) →
        ∃ B : Subgroup (Automizer V),
          FactorSeed (automizerRepresentation V) (inducedAutomizer V X) B) :
    (localM V : ℕ∞) ≤ globalR V ∧
      globalS V = (localM V : ℕ∞) ∧ 2 < globalS V := by
  exact lower_bound_of_earlier_sources h hm
    (InvariantSubspaces.source_commonNormalInput_of_A312 T hA312)
    source_localContainment (source_residualNormalization KnownSimple.IsKnownSimple)
    ho h67 h68 h23 h11 hONan

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
