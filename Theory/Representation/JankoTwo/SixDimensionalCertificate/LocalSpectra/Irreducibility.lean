module

public import Theory.Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.WeightDecomposition
public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Absolute irreducibility of faithful Hall--Janko representations of degree six

The zero weight vanishes. Any subrepresentation inherits a rotation-invariant
weight function, so its dimension is divisible by six. Thus no nonzero proper
subrepresentation exists. Extension to the algebraic closure preserves both
faithfulness and dimension and gives the assertion over any characteristic-two
field. This argument does not require the later cubic exclusion.

Source: Aschbacher--Smith K.4.5, printed p.460; Hiss--Malle corrected
Table 2, the characteristic-two degree-six J₂ entry. See ../Source.md.
-/

@[expose] public noncomputable section

namespace Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra
open Sporadic.LeechRelated.J2 Polynomial
open scoped BigOperators DirectSum
variable {E U : Type*} [Field E] [AddCommGroup U] [Module E U]

/-- Restricting a representation cannot increase any simultaneous multiplicity. -/
theorem weightMultiplicity_subrepresentation_le [FiniteDimensional E U]
    (ρ : Representation E Carrier U) (S : Subrepresentation ρ) (ζ : E) (w : Weights.Weight) :
    weightMultiplicity S.toRepresentation ζ w ≤ weightMultiplicity ρ ζ w := by
  let f : weightSpace S.toRepresentation ζ w →ₗ[E] weightSpace ρ ζ w :=
    (S.toSubmodule.subtype.comp (weightSpace S.toRepresentation ζ w).subtype).codRestrict _ (by
      intro v
      constructor
      · apply Module.End.mem_eigenspace_iff.mpr
        exact congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp v.property.1)
      · apply Module.End.mem_eigenspace_iff.mpr
        exact congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp v.property.2))
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  intro a b h
  exact Subtype.ext (Subtype.ext (congrArg (fun z => (z.val : U)) h))

/-- The order-six normalizer makes every nonzero subrepresentation have degree at least six. -/
theorem isIrreducible_of_faithful_six_with_root [CharP E 2] [IsAlgClosed E]
    [FiniteDimensional E U] (ρ : Representation E Carrier U) (hρ : Function.Injective ρ)
    (hdim : Module.finrank E U = 6) {ζ : E} (hζ : IsPrimitiveRoot ζ 5) :
    IsIrreducible ρ := by
  obtain ⟨i, hi⟩ := four_patterns ρ hρ hdim hζ
  have hz : weightMultiplicity ρ ζ 0 = 0 := (hi 0).trans (Weights.pattern_zero i)
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have he : (⊥ : Submodule E U) = ⊤ := congrArg Subrepresentation.toSubmodule h
    have hh := congrArg (fun S : Submodule E U => Module.finrank E S) he
    simp only [finrank_bot, finrank_top, hdim] at hh
    omega
  · intro S
    by_cases ht : S = ⊤
    · exact Or.inr ht
    left
    have hst : S.toSubmodule ≠ ⊤ := by
      intro h
      exact ht (Subrepresentation.toSubmodule_injective h)
    have hlt := S.toSubmodule.finrank_lt hst
    rw [hdim] at hlt
    have hs0 : weightMultiplicity S.toRepresentation ζ 0 = 0 := by
      have hh := weightMultiplicity_subrepresentation_le ρ S ζ 0
      omega
    have hs := Weights.sum_rotation_invariant (weightMultiplicity S.toRepresentation ζ)
      (weightMultiplicity_rotate S.toRepresentation hζ)
    rw [sum_weightMultiplicity S.toRepresentation hζ, hs0] at hs
    have hdimS : Module.finrank E S.toSubmodule = 0 := by omega
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.finrank_eq_zero.mp hdimS

/-- Every faithful six-dimensional characteristic-two action over an algebraically
closed field is irreducible, independently of the later cubic exclusion. -/
theorem isIrreducible_of_faithful_six [CharP E 2] [IsAlgClosed E] [FiniteDimensional E U]
    (ρ : Representation E Carrier U) (hρ : Function.Injective ρ)
    (hdim : Module.finrank E U = 6) : IsIrreducible ρ := by
  let : NeZero (5 : E) := ⟨(CharP.cast_eq_zero_iff E 2 5).not.mpr (by decide)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot E 5
  exact isIrreducible_of_faithful_six_with_root ρ hρ hdim hζ

/-- Scalar extension proves absolute irreducibility over an arbitrary field of
characteristic two. No scalar-descent or small-module catalogue premise is used. -/
theorem isAbsolutelyIrreducible_of_faithful_six [CharP E 2] [FiniteDimensional E U]
    (ρ : Representation E Carrier U) (hρ : Function.Injective ρ)
    (hdim : Module.finrank E U = 6) : IsAbsolutelyIrreducible ρ := by
  refine ⟨isIrreducible_of_faithful_six (extendScalars (AlgebraicClosure E) ρ)
    ((extendScalars_faithful_iff (AlgebraicClosure E) ρ).mp hρ) ?_⟩
  simpa only [Module.finrank_baseChange] using hdim


end Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra
