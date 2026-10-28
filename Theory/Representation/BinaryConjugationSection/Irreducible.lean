module
public import Theory.Representation.BinaryConjugationSection.InvariantPreimage
public import Theory.Representation.SubrepresentationLattice

/-!
# Irreducibility from minimality of the original section

Every invariant vector subspace pulls back through the specified quotient
coordinates to an actor-invariant subgroup. Thus subgroup minimality above
the kernel proves irreducibility of this exact marked action.

Source: Aschbacher–Smith, A.1.40 and the use of D.3.6 in10.1.1,
printed pp.31,196 and741.
-/

@[expose] public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H R Z : Subgroup G}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) H V} (d : BinaryConjugationSection H R Z ρ)

include d in
/-- The subgroup criterion retains the section's original coordinate map. -/
theorem irreducible_of_subgroup_minimal [Nontrivial V]
    (hmin : ∀ J : Subgroup G, J ≤ R → H ≤ normalizer (J : Set G) →
      J = R ∨ J ≤ Z) : ρ.IsIrreducible := by
  refine ⟨?_⟩
  intro P
  rcases hmin (d.invariantPreimage P) (d.invariantPreimage_le P)
      (d.invariantPreimage_normalized P) with he | hz
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    obtain ⟨r, hr⟩ := d.onto (Multiplicative.ofAdd v)
    have hm : (r : G) ∈ d.invariantPreimage P := he.symm ▸ r.property
    obtain ⟨_, hp⟩ := (d.mem_invariantPreimage P r).mp hm
    simpa only [hr, toAdd_ofAdd] using hp
  · left
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    obtain ⟨r, hr⟩ := d.onto (Multiplicative.ofAdd v)
    have hm : (r : G) ∈ d.invariantPreimage P :=
      (d.mem_invariantPreimage P r).mpr ⟨r.property, by simpa only [hr, toAdd_ofAdd] using hv⟩
    have he := (d.coordinates_eq_one_iff r).mpr (hz hm)
    change v = 0
    exact congrArg Multiplicative.toAdd (hr.symm.trans he)

end Representation.BinaryConjugationSection
