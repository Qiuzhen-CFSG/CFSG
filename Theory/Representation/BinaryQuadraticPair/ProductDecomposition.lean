module

public import Theory.Representation.BinaryQuadraticPair.ProductMarks
public import Theory.Representation.BinaryQuadraticPair.ProductDecomposition.Separation
public import Theory.Representation.BinaryQuadraticPair.ProductDecomposition.FiniteSums

/-!
# The two natural summands of a quadratic S₃ × S₃ action

The mixed quadratic identity and zero common odd fixed space split a binary
product representation into its two ordered factor commutator spaces. Each
space is fixed by the opposite factor and is a finite sum of concrete natural
modules for its own factor. The two multiplicities are independent and may
be zero. The maps intertwine the full product action.

`ProductDecomposition.of_mixed_quadratic` constructs all these conclusions.
`ProductMark.decomposition` and `ProductMark.exists_decomposition` apply it
to the marked quadratic configuration, discharging both representation-theoretic
premises from the existing mark record. The actual quotient configuration
is constructed by the Chapter G consumer; no new premise is imposed here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.2.6(5), printed p.336, PDF p.347, 1 March 2004 manuscript.
-/

@[expose] public section

open InvertedCubicTensor
namespace Representation.BinaryQuadraticPair
variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The two ordered natural-module sums, with the literal commutator and
fixed-space descriptions. The multiplicities may independently be zero. -/
structure ProductDecomposition (ρ : Representation F (S₃ × S₃) V) where
  left : Subrepresentation ρ
  right : Subrepresentation ρ
  complementary : IsCompl left.toSubmodule right.toSubmodule
  left_commutator : left.toSubmodule =
    BinaryOffender.subspaceCommutator ρ ⊤ ProductDecomposition.leftFactor
  right_commutator : right.toSubmodule =
    BinaryOffender.subspaceCommutator ρ ⊤ ProductDecomposition.rightFactor
  left_fixed : left.toSubmodule = BinaryOffender.fixedSpace ρ ProductDecomposition.rightFactor
  right_fixed : right.toSubmodule = BinaryOffender.fixedSpace ρ ProductDecomposition.leftFactor
  leftMultiplicity : ℕ
  rightMultiplicity : ℕ
  leftEquiv : (Fin leftMultiplicity → BinaryPermutation.core (Fin 3)) ≃ₗ[F] left.toSubmodule
  rightEquiv : (Fin rightMultiplicity → BinaryPermutation.core (Fin 3)) ≃ₗ[F] right.toSubmodule
  left_equivariant : ∀ (g : S₃ × S₃) x,
    leftEquiv (fun j => BinaryPermutation.coreRepresentation (Fin 3) g.1 (x j)) =
      left.toRepresentation g (leftEquiv x)
  right_equivariant : ∀ (g : S₃ × S₃) x,
    rightEquiv (fun j => BinaryPermutation.coreRepresentation (Fin 3) g.2 (x j)) =
      right.toRepresentation g (rightEquiv x)

namespace ProductDecomposition
variable (ρ : Representation F (S₃ × S₃) V) [FiniteDimensional F V]

/-- Mixed quadraticity and the vanishing common odd fixed space give the
complete ordered decomposition into finite sums of concrete natural modules. -/
noncomputable def of_mixed_quadratic
    (t₁ t₂ : S₃) (hs₁ : t₁ * t₁ = 1) (hn₁ : t₁ ≠ 1)
    (hs₂ : t₂ * t₂ = 1) (hn₂ : t₂ ≠ 1)
    (hm : (ρ (t₁, 1) - 1) * (ρ (1, t₂) - 1) = 0)
    (h0 : BinaryOffender.fixedSpace ρ
      ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))) = ⊥) :
    ProductDecomposition ρ := by
  let hl := leftSummand_fixedFree ρ h0
  let hr := rightSummand_fixedFree ρ h0
  have hcross := mixed_all ρ t₁ t₂ hs₁ hn₁ hs₂ hn₂ hm
  refine {
    left := leftSummand ρ
    right := rightSummand ρ
    complementary := summands_isCompl ρ hcross h0
    left_commutator := (moved_eq_fixed ρ hcross h0).1.symm
    right_commutator := (moved_eq_fixed ρ hcross h0).2.symm
    left_fixed := rfl
    right_fixed := rfl
    leftMultiplicity := naturalMultiplicity (leftAction (leftSummand ρ).toRepresentation)
    rightMultiplicity := naturalMultiplicity (rightAction (rightSummand ρ).toRepresentation)
    leftEquiv := naturalSumEquiv _ hl
    rightEquiv := naturalSumEquiv _ hr
    left_equivariant := ?_
    right_equivariant := ?_ }
  · intro g x
    rw [leftSummand_action]
    exact naturalSumEquiv_equivariant _ hl g.1 x
  · intro g x
    rw [rightSummand_action]
    exact naturalSumEquiv_equivariant _ hr g.2 x

omit [FiniteDimensional F V] in
/-- The finite-sum realization computes each dimension with its own multiplicity. -/
theorem finranks (d : ProductDecomposition ρ) :
    Module.finrank F d.left.toSubmodule = 2 * d.leftMultiplicity ∧
      Module.finrank F d.right.toSubmodule = 2 * d.rightMultiplicity := by
  constructor
  · rw [← d.leftEquiv.finrank_eq, Module.finrank_pi_fintype]
    simp [natural_finrank, mul_comm]
  · rw [← d.rightEquiv.finrank_eq, Module.finrank_pi_fintype]
    simp [natural_finrank, mul_comm]

end ProductDecomposition

namespace ProductMark
variable [FiniteDimensional F V] {ρ : Representation F (S₃ × S₃) V}
  {A : Submodule F V} {t₁ t₂ : S₃} {a : S₃ × S₃}

/-- Apply the product recognition directly to the marked configuration.
This consumes precisely the record constructed by G.2.6's literal quotient
configuration; no fixed-space or natural-module recognition premise remains. -/
noncomputable def decomposition (h : ProductMark ρ A t₁ t₂ a) : ProductDecomposition ρ :=
  ProductDecomposition.of_mixed_quadratic ρ t₁ t₂ h.left_square h.left_ne_one
    h.right_square h.right_ne_one h.mixed_quadratic h.common_fixed_eq_bot

/-- Existence form of the marked-configuration consumer. -/
theorem exists_decomposition (h : ProductMark ρ A t₁ t₂ a) :
    Nonempty (ProductDecomposition ρ) := ⟨h.decomposition⟩

end ProductMark
end Representation.BinaryQuadraticPair
