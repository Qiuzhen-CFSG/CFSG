module

public import Theory.Representation.BinaryPolarity.SymmetricSix
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual

/-!
# The field-natural alternating five inside binary Sp₄

The trace-determinant form on the literal F₄² module is alternating and
nondegenerate. Its symplectic coordinates construct a faithful embedding of
SL₂(4) into the actual binary symplectic matrix group. The displayed equation
retains every matrix and vector; no group identification from order is used.

This is the native exceptional A₅ needed in the six-letter polar action. The
six-letter transitivity and actual subgroup are supplied in the next module.
-/

public section
namespace Theory.SpecificGroups.SymmetricSix.ExceptionalAlternatingFive

open Representation.SL2FourNatural
open scoped Matrix

private theorem trace_form_alt : binaryPairing.IsAlt := by
  intro v
  rw [binaryPairing_apply, wedge, mul_comm (v 0) (v 1), sub_self, map_zero]

private theorem trace_form_nondegenerate : binaryPairing.Nondegenerate := by
  constructor
  · intro v hv
    apply binaryPairing_injective
    apply LinearMap.ext
    intro w
    simpa only [map_zero, LinearMap.zero_apply] using hv w
  · change ∀ v : V, (∀ w : V, QuadraticAlgebra.trace (wedge w v) = 0) → v = 0
    decide +kernel

/-- An actual faithful binary symplectic embedding, with the original
field-natural action and a specified linear coordinate map. -/
theorem exists_marked_symplectic_embedding :
    ∃ e : V ≃ₗ[ZMod 2] NaturalModule,
      ∃ φ : SL →* Matrix.PSp4Three.Sp 2 (ZMod 2), Function.Injective φ ∧
        ∀ g v, (φ g).val *ᵥ (e v) = e (action g v) := by
  have hf : Function.Injective naturalRepresentation := by
    intro g h hgh
    apply action_faithful
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun hgh v
  obtain ⟨e,φ,hφ,he⟩ := BinaryPolarity.exists_marked_symplectic_action_of_form
    naturalRepresentation hf finrank_vector binaryPairing trace_form_alt
    trace_form_nondegenerate binaryPairing_invariant
  exact ⟨e.toLinearEquiv,φ,hφ,he⟩

end Theory.SpecificGroups.SymmetricSix.ExceptionalAlternatingFive
