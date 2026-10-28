module

public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# First cohomology from a cyclic cocycle normal form

If every crossed homomorphism is a scalar multiple of one fixed cocycle plus
a principal cocycle, and the fixed cocycle is not principal, its class gives
an explicit linear isomorphism from the coefficient field to first cohomology.
Restriction from a field of order `p^n` to its prime field then gives dimension
`n`. Neither the cocycle decomposition nor its nonprincipality is inferred
from a desired dimension: both are explicit inputs to the criterion.

This is the elementary quotient step for the natural-module calculations in
Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma I.1.6,
printed p.408; the family-specific cocycle calculations are separate.
-/

@[expose] public section

namespace Representation.OneCohomology

section NormalForm
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (c : cocycles ρ)
  (hnonprincipal : ¬ ∃ v, principal ρ v = c)
  (hspans : ∀ f : cocycles ρ, ∃ a : k, ∃ v : V, f = a • c + principal ρ v)

/-- The class of a nonprincipal cocycle with this normal form is a basis of `H1`. -/
noncomputable def H1EquivOfCyclicNormalForm : k ≃ₗ[k] H1 ρ :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton k (H1 ρ) (classMap ρ c)) (by
    constructor
    · exact smul_left_injective k (by
        intro h
        exact hnonprincipal ((classMap_eq_zero_iff ρ c).mp h))
    · intro x
      obtain ⟨f, rfl⟩ := (principal ρ).range.mkQ_surjective x
      obtain ⟨a, v, rfl⟩ := hspans f
      refine ⟨a, ?_⟩
      change a • classMap ρ c = classMap ρ (a • c + principal ρ v)
      rw [map_add, map_smul,
        (classMap_eq_zero_iff ρ (principal ρ v)).mpr ⟨v, rfl⟩, add_zero])

include hnonprincipal hspans in
lemma finrank_H1_of_cyclicNormalForm : Module.finrank k (H1 ρ) = 1 := by
  rw [← (H1EquivOfCyclicNormalForm ρ c hnonprincipal hspans).finrank_eq,
    Module.finrank_self]

end NormalForm

section PrimeField
variable {K G V : Type*} [Field K] [Finite K] [Group G]
  [AddCommGroup V] [Module K V]
  (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K]
  [Module (ZMod p) V] [IsScalarTower (ZMod p) K V]

/-- Convert the order of a finite coefficient field into its prime-field degree. -/
lemma coefficient_finrank_of_card (n : ℕ) (hcard : Nat.card K = p ^ n) :
    Module.finrank (ZMod p) K = n := by
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  exact (FiniteField.pow_finrank_eq_natCard p K).trans hcard

/-- A cyclic cocycle normal form over a field of order `p^n` gives prime-field
first-cohomology dimension `n` for the restricted representation. -/
lemma finrank_restrictScalars_of_cyclicNormalForm
    (ρ : Representation K G V) (n : ℕ) (hcard : Nat.card K = p ^ n)
    (c : cocycles ρ) (hnonprincipal : ¬ ∃ v, principal ρ v = c)
    (hspans : ∀ f : cocycles ρ, ∃ a : K, ∃ v : V, f = a • c + principal ρ v) :
    Module.finrank (ZMod p) (H1 (restrictScalars (k := ZMod p) ρ)) = n := by
  rw [finrank_restrictScalars, finrank_H1_of_cyclicNormalForm ρ c hnonprincipal hspans,
    mul_one, coefficient_finrank_of_card p n hcard]

end PrimeField
end Representation.OneCohomology
