module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.Commutator.ConjugateSpan
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.Representation.BinaryPermutation.FiveQuadratic

/-!
# Field components in the §13.8 sieve

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Lemmas 13.8.19–21, printed pp.953–957.

The completed deductions here use the actual source conjugate span and quotient.
The commutator-generated seed gives clause 13.8.21(4) once the containment in a
component is established. A simple normal component with two-group quotient in
`H/O₂(H)` is its generalized Fitting subgroup and belongs to every nontrivial
normal subgroup, supplying the input for faithful actions on sections.

`BinaryPermutation.FiveQuadratic.not_quadratic_of_noncentral_quotient` supplies
the last permutation-module contradiction in the L₂(4) branch, with an actual
S₅ isomorphism, equivariant surjection, and marked double transpositions.

These deductions do not yet establish the numbered source results. The L₃(2)
exclusion, Borel two-residual and torus calculations, external-X case, exceptional
SL₃(4) and (S)U₃(8) cases, central-cover and M₂₂ exclusions, and L₁ containment
remain obligations of the field-component assembly. In particular simplicity
and the two-group quotient in the theorem below must still be derived from
the complete component list and the remaining source arguments.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The generation step in 13.8.21(4), from the earlier seed identity used
in 13.7.5(2). `X` is L₁ or L₁,+, as appropriate. Only normality inside H
is required. The field-component exclusions must still establish `X ≤ K`. -/
theorem UH_eq_commutator_of_seed
    (H K X V₃ : Subgroup G) (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    (hXK : X ≤ K) (hseed : V₃ = ⁅V₃, X⁆) :
    Source.UH H V₃ = ⁅Source.UH H V₃, K⁆ :=
  conjugateSpanBy_eq_commutator_of_seed V₃ H K X hKH
    (le_normalizer_of_normal_subgroupOf hKH) hXK hseed

/-- The normal-subgroup consequence following 13.8.21, for the actual
quotient H*. Its trivial two-core is proved, not an extra assumption.
The component and outer-quotient hypotheses remain explicit until assembly. -/
theorem Hstar_structure_of_simple_component [Finite G]
    (H K : Subgroup G) [(Source.starImage H K).Normal]
    [IsSimpleGroup (Source.starImage H K)]
    (ha : ¬ IsMulCommutative (Source.starImage H K))
    (hquot : IsPGroup 2 (Source.Hstar H ⧸ Source.starImage H K)) :
    generalizedFitting (Source.Hstar H) = Source.starImage H K ∧
      centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥ ∧
      ∀ N : Subgroup (Source.Hstar H),
        N.Normal → N ≠ ⊥ → Source.starImage H K ≤ N := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact simple_two_quotient_structure (Source.starImage H K) ha hquot
    (pCore_quotient_pCore_eq_bot 2)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
