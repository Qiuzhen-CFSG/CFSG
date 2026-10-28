module

public import Theory.Representation.GoldschmidtONan.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# Transport in the TI fixed-space orbit

The representation transports the actual orbit subspaces bijectively, preserves
their dimensions and cardinalities, and permutes the suborbits of the cyclic
actor. A common nonzero vector identifies two orbit members by the TI hypothesis.
These are the transport facts used in Steps 1–2 of GLS, Number 2, Chapter C,
Proposition 14.2 (`refs/KGroup/GLS2/ChapterC.tex`).
-/

public section
namespace Representation.GoldschmidtONan
open BinaryOffender RegularCyclicNormalClosure
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

/-- Composition of images follows the left representation action. -/
theorem orbit_map_mul (W : Submodule (ZMod 2) V) (a b : X) :
    W.map (ρ (a * b)) = (W.map (ρ b)).map (ρ a) := by
  rw [← Submodule.map_comp, map_mul]
  rfl

/-- Acting by the identity preserves every subspace. -/
@[simp] theorem orbit_map_one (W : Submodule (ZMod 2) V) :
    W.map (ρ (1 : X)) = W := by
  simp only [map_one]
  exact Submodule.map_id _

/-- Each group element induces an injective permutation of subspaces. -/
theorem orbit_map_injective (x : X) :
    Function.Injective (fun W : Submodule (ZMod 2) V => W.map (ρ x)) := by
  intro U W he
  have hh := congrArg (fun S : Submodule (ZMod 2) V => S.map (ρ x⁻¹)) he
  simpa only [← orbit_map_mul, inv_mul_cancel, orbit_map_one] using hh

/-- The fixed space belongs to its actual orbit. -/
theorem fixed_mem_fixedOrbit : fixedSpace ρ Y ∈ fixedOrbit ρ Y :=
  ⟨1, orbit_map_one _⟩

/-- The actual orbit is closed under the representation. -/
theorem map_mem_fixedOrbit {W : Submodule (ZMod 2) V} (hW : W ∈ fixedOrbit ρ Y)
    (x : X) : W.map (ρ x) ∈ fixedOrbit ρ Y := by
  obtain ⟨a, rfl⟩ := hW
  exact ⟨x * a, orbit_map_mul _ _ _⟩

/-- Any two members of the actual orbit are related by an acting element. -/
theorem exists_map_eq_of_mem_fixedOrbit {U W : Submodule (ZMod 2) V}
    (hU : U ∈ fixedOrbit ρ Y) (hW : W ∈ fixedOrbit ρ Y) :
    ∃ x : X, U.map (ρ x) = W := by
  obtain ⟨a, rfl⟩ := hU
  obtain ⟨b, rfl⟩ := hW
  refine ⟨b * a⁻¹, ?_⟩
  rw [← orbit_map_mul, inv_mul_cancel_right]

/-- All orbit members have the cardinality of the fixed space. -/
theorem card_eq_fixed_of_mem_fixedOrbit {W : Submodule (ZMod 2) V}
    (hW : W ∈ fixedOrbit ρ Y) : Nat.card W = Nat.card (fixedSpace ρ Y) := by
  obtain ⟨x, rfl⟩ := hW
  exact (Nat.card_congr (Submodule.equivMapOfInjective (ρ x)
    (action_injective x) (fixedSpace ρ Y)).toEquiv).symm

/-- All orbit members have the dimension of the fixed space. -/
theorem finrank_eq_fixed_of_mem_fixedOrbit {W : Submodule (ZMod 2) V}
    (hW : W ∈ fixedOrbit ρ Y) :
    Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) (fixedSpace ρ Y) := by
  obtain ⟨x, rfl⟩ := hW
  exact (Submodule.equivMapOfInjective (ρ x)
    (action_injective x) (fixedSpace ρ Y)).finrank_eq.symm

/-- A common nonzero vector identifies two members of a TI orbit. -/
theorem Input.orbit_eq_of_common_nonzero (h : Input ρ Y)
    {U W : Submodule (ZMod 2) V} (hU : U ∈ fixedOrbit ρ Y)
    (hW : W ∈ fixedOrbit ρ Y) {v : V} (hvU : v ∈ U) (hvW : v ∈ W) (hv : v ≠ 0) :
    U = W := by
  by_contra hne
  exact hv (Submodule.disjoint_def.mp (h.ti U hU W hW hne) v hvU hvW)

/-- An orbit member distinct from the fixed space is disjoint from it. -/
theorem Input.orbit_disjoint_fixed (h : Input ρ Y) {W : Submodule (ZMod 2) V}
    (hW : W ∈ fixedOrbit ρ Y) (hne : W ≠ fixedSpace ρ Y) :
    Disjoint W (fixedSpace ρ Y) := h.ti W hW _ fixed_mem_fixedOrbit hne

/-- The actor fixes its fixed space pointwise, hence setwise. -/
theorem fixed_map_actor (y : Y) : (fixedSpace ρ Y).map (ρ y) = fixedSpace ρ Y := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    rwa [show ρ y v = v from hv y]
  · intro v hv
    exact ⟨v, hv, hv y⟩

/-- Only invariance under Y is used for the moved space in Step 1. -/
theorem moved_map_actor (y : Y) :
    (displacementSpan ρ Y ⊤).map (ρ y) = displacementSpan ρ Y ⊤ :=
  displacementSpan_map_of_normalized ρ Y y
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Y.le_normalizer y.property))

/-- Acting by Y preserves membership in its moved space in both directions. -/
theorem mem_moved_action_iff (y : Y) (v : V) :
    ρ y v ∈ displacementSpan ρ Y ⊤ ↔ v ∈ displacementSpan ρ Y ⊤ := by
  constructor
  · intro hv
    have hh := moved_mem_action y⁻¹ hv
    simpa only [Subgroup.coe_inv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using hh
  · exact moved_mem_action y

/-- The Y-image of a nonfixed orbit member is still distinct from the fixed space. -/
theorem map_actor_ne_fixed {W : Submodule (ZMod 2) V}
    (hne : W ≠ fixedSpace ρ Y) (y : Y) : W.map (ρ y) ≠ fixedSpace ρ Y := by
  intro he
  apply hne
  exact orbit_map_injective (y : X) (he.trans (fixed_map_actor y).symm)

/-- Orbit members are nonzero whenever the fixed space is nonzero. -/
theorem Input.orbit_ne_bot (h : Input ρ Y) {W : Submodule (ZMod 2) V}
    (hW : W ∈ fixedOrbit ρ Y) : W ≠ ⊥ := by
  obtain ⟨x, rfl⟩ := hW
  intro he
  apply h.fixed_nontrivial
  exact orbit_map_injective x (he.trans (Submodule.map_bot _).symm)

end Representation.GoldschmidtONan
