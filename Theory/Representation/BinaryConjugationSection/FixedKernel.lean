module
public import Theory.Representation.BinaryConjugationSection
/-!
# Centralizing subgroups and fixed-free module coordinates

A vector coming from an element centralizing the actor is fixed by the
whole representation. If the representation has zero fixed space, this
element lies in the specified coordinate kernel. In particular, a faithful
whole-module marking makes the actor-centralizing subgroup trivial.

Source: the fixed-kernel step in Aschbacher--Smith, 10.1.1--2,
printed pp.741--742.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {R A Z : Subgroup G}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) R V}

/-- Absence of global fixed vectors places the literal actor-centralizing
subgroup inside the retained coordinate kernel. -/
theorem centralizer_le_kernel_of_fixed_eq_zero
    (d : BinaryConjugationSection R A Z ρ)
    (hzero : ∀ v, (∀ r, ρ r v = v) → v = 0) :
    A ⊓ centralizer (R : Set G) ≤ Z := by
  intro a ha
  let w : A := ⟨a,ha.1⟩
  apply (d.coordinates_eq_one_iff w).mp
  apply Multiplicative.toAdd.injective
  apply hzero
  intro r
  have he := d.equivariant r w
  have hw : (⟨r*w*(r:G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized r.property) w).mp w.property⟩ : A) = w := by
    apply Subtype.ext
    change (r:G)*a*(r:G)⁻¹ = a
    rw [ha.2 r r.property,mul_inv_cancel_right]
  rw [hw] at he
  exact he.symm
end Representation.BinaryConjugationSection
