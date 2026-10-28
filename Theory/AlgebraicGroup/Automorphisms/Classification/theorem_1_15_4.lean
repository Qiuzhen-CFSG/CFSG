module

public import Theory.AlgebraicGroup.Automorphisms.Classification.theorem_1_15_2
public import Theory.AlgebraicGroup.Automorphisms.Classification.ExceptionalRootBijection

/-!
This module isolates `theorem_1_15_4` from `Theory.AlgebraicGroup.Automorphisms.Classification`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_15_4
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T)
    (C : ChevalleyData K D) (hK : IsSimpleAlgebraicGroup K)
    (setup : SteinbergChevalleyRootSystem D C)
    (classification : RootClassification)
    (hClass : D.HasDynkinClassificationForSteinberg classification)
    (hchar : ringChar k ≠ 0) :
    ∃ family : FrobeniusAutomorphismFamily D C,
      (∀ a : ℤ, ∃! φ : Aut K,
        IsFrobeniusGeneratorFormula D C family.scalarSystem a φ) ∧
      (∀ a : ℤ,
        HasAlgebraicEndomorphismRealization (family.automorphism a) ↔ 0 ≤ a) ∧
      (∀ a : ℤ,
        family.automorphism a ∈ SteinbergAutomorphismSet K ↔ 0 < a) ∧
      (IsExceptionalSteinbergType classification (ringChar k) →
        ∃! ρ : Equiv.Perm D.Root,
          IsAnglePreservingLengthChangingRootBijection D ρ) ∧
      (IsExceptionalSteinbergType classification (ringChar k) →
        ∀ ρ, IsAnglePreservingLengthChangingRootBijection D ρ →
          ∃! ψ : Aut K, IsExceptionalGraphFieldFormula D C family ρ ψ) ∧
      (IsExceptionalSteinbergType classification (ringChar k) →
        ∀ ρ ψ, IsAnglePreservingLengthChangingRootBijection D ρ →
          IsExceptionalGraphFieldFormula D C family ρ ψ →
          ψ ∈ SteinbergAutomorphismSet K ∧ ψ ^ 2 = family.automorphism 1) := by sorry

public def AbstractAutomorphismsCommuteWith
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (pi : AlgebraicGroup.Morphism G H) (sigmaG : Aut G) (sigmaH : Aut H) : Prop :=
  ∀ x, pi.onPoints (sigmaG x) = sigmaH (pi.onPoints x)

end Theory.AlgebraicGroup
