module
public import Mathlib.RepresentationTheory.Intertwining
/-!
# Removing an actual inner action

An actor inducing conjugation by a homomorphism into the component splits
as that inner operator times a commuting representation. The full original
actor is retained; no passage to a faithful action image occurs.

Source application: the Suzuki Steinberg isotypic part in Aschbacher–Smith
§13.6, printed p.935.
-/

public noncomputable section
open Module Representation
namespace Representation
variable {k D A V : Type*} [Field k] [Group D] [Group A]
  [AddCommGroup V] [Module k V]

/-- Remove an actual inner action to obtain the commuting multiplicity actor. -/
def innerUntwist (ρ : Representation k D V) (τ : Representation k A V)
    (φ : A →* D)
    (hc : ∀ a d, τ a * ρ d = ρ (φ a * d * (φ a)⁻¹) * τ a) :
    Representation k A V where
  toFun a := ρ (φ a)⁻¹ * τ a
  map_one' := by simp
  map_mul' a b := by
    change ρ (φ (a*b))⁻¹ * τ (a*b) = (ρ (φ a)⁻¹ * τ a) * (ρ (φ b)⁻¹ * τ b)
    rw [mul_assoc, ← mul_assoc (τ a), hc]
    simp only [map_mul, mul_inv_rev]
    simp only [← mul_assoc, ← map_mul]
    simp only [inv_mul_cancel, one_mul, map_mul, mul_assoc]

/-- The untwisted action commutes with every original component operator. -/
theorem innerUntwist_commute (ρ : Representation k D V) (τ : Representation k A V)
    (φ : A →* D)
    (hc : ∀ a d, τ a * ρ d = ρ (φ a * d * (φ a)⁻¹) * τ a)
    (a : A) (d : D) :
    innerUntwist ρ τ φ hc a * ρ d = ρ d * innerUntwist ρ τ φ hc a := by
  change (ρ (φ a)⁻¹ * τ a) * ρ d = ρ d * (ρ (φ a)⁻¹ * τ a)
  rw [mul_assoc, hc]
  simp only [← mul_assoc, ← map_mul]
  congr 2
  simp only [inv_mul_cancel, one_mul]

/-- The original actor is recovered by the actual inner factor. -/
theorem innerUntwist_reconstruct (ρ : Representation k D V) (τ : Representation k A V)
    (φ : A →* D)
    (hc : ∀ a d, τ a * ρ d = ρ (φ a * d * (φ a)⁻¹) * τ a) (a : A) :
    τ a = ρ (φ a) * innerUntwist ρ τ φ hc a := by
  change τ a = ρ (φ a) * (ρ (φ a)⁻¹ * τ a)
  rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
end Representation
