module

public import Theory.LinearAlgebra.BinaryPolarity
import all Theory.LinearAlgebra.BinaryPolarity

/-!
# Evaluating the form reconstructed from a binary polarity

This extension exposes the evaluation equation without changing the existing
form's abstraction boundary. Its proof intentionally uses the implementation
of the same-package polarity construction; clients only need the equation.
-/

public section
namespace BinaryPolarity
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem form_apply_nonzero
    (f : {x : V // x ≠ 0} → V →ₗ[ZMod 2] ZMod 2)
    (hs : ∀ x y : {x : V // x ≠ 0}, f x y = 0 ↔ f y x = 0)
    {x : V} (hx : x ≠ 0) (y : V) : form f hs x y = f ⟨x, hx⟩ y := by
  change pairing f x y = _
  rw [pairing_nonzero f hx]
end BinaryPolarity
