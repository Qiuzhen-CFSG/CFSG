module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.Orientation
public import Theory.Representation.EndFieldFrobenius

/-!
# From tensor uniqueness and coefficient transport to exact periods

This is a conditional assembly lemma, not the Steinberg classification. Its
three representation-theoretic premises must be proved for the actual tensor
family: irreducibility, parameter uniqueness, and intertwining equivalences
for coefficient Frobenius. The coefficient premise uses the *left* shift of
the forward-wrapped sequence; applying Frobenius to that shifted tensor
returns the original tensor. This keeps the inverse graph twist at exponent
overflow consistent with `TensorData`'s forward wrap.

The proof uses the modular irreducible trace-equivalence theorem and the
injectivity of coefficient Frobenius. The reverse implication follows directly
from the supplied intertwiner. No restriction theorem is asserted here.

Source: GLS3, Remark 2.8.8.
-/

public section

namespace Triality.RestrictedWeights.SteinbergTensors
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {G : Type v} [Group G]

/-- The exact period conclusion, conditional on the three separately required
representation theorems. Final source assembly must discharge all three. -/
theorem character_period_of_classification_and_coefficient_equiv
    {n : ℕ} (hn : 0 < n) (R : (Fin n → BasicWeight) → FDRep k G)
    (hirr : ∀ a, Representation.IsIrreducible (R a).ρ)
    (hunique : ∀ a b,
      Nonempty (Representation.Equiv (R a).ρ (R b).ρ) → a = b)
    (hcoeff : ∀ a r,
      Nonempty (Representation.Equiv
        (Representation.frobeniusConjugate 2 r (R (shiftWeights hn a r)).ρ) (R a).ρ))
    (a : Fin n → BasicWeight) (r : ℕ) :
    (∀ g, Representation.character (R a).ρ g ^ (2 ^ r) =
      Representation.character (R a).ρ g) ↔
        Function.Periodic (extendWeights hn a) r := by
  obtain ⟨e⟩ := hcoeff a r
  have htrace (g : G) :
      Representation.character (R (shiftWeights hn a r)).ρ g ^ (2 ^ r) =
        Representation.character (R a).ρ g := by
    rw [← Representation.character_frobeniusConjugate 2 r]
    exact congrFun (Representation.char_iso e) g
  rw [← shiftWeights_eq_iff hn a r]
  constructor
  · intro hfixed
    have hchar : Representation.character (R (shiftWeights hn a r)).ρ =
        Representation.character (R a).ρ := by
      funext g
      apply (iterateFrobeniusEquiv k 2 r).injective
      change Representation.character (R (shiftWeights hn a r)).ρ g ^ (2 ^ r) =
        Representation.character (R a).ρ g ^ (2 ^ r)
      rw [htrace g, hfixed g]
    let := hirr (shiftWeights hn a r)
    let := hirr a
    exact hunique _ _ ((Representation.character_eq_iff_equiv_of_irreducible _ _).mp hchar)
  · intro hshift g
    have h := htrace g
    rw [hshift] at h
    exact h

end Triality.RestrictedWeights.SteinbergTensors
