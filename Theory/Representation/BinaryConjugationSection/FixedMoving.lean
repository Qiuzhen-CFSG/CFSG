module
public import Theory.Representation.BinaryConjugationSection
public import Mathlib.GroupTheory.Commutator.Basic
public import Theory.Representation.FirstCohomology
/-!
# Fixed-moving vectors in the original group section

The coordinate action fixes a vector exactly when the corresponding ambient
commutator lies in the specified kernel. Thus a vector fixed by S and moved
by K lifts to the same fixed-moving configuration in W/Z. The kernel may
contain nonzero fixed vectors; no fixed-free hypothesis is used.

The consumer is the five-dimensional central-cover branch of
Aschbacher--Smith 14.6.24, using I.2.3 on its original ambient action.
-/

public section
open Subgroup Representation.OneCohomology
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H W Z : Subgroup G}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {τ : Representation (ZMod 2) H V}

theorem fixed_coordinate_iff_commutator_mem
    (c : BinaryConjugationSection H W Z τ) (a : H) (u : W) :
    τ a (c.coordinates u).toAdd = (c.coordinates u).toAdd ↔
      ⁅(u : G),(a : G)⁆ ∈ Z := by
  let v : W := ⟨(a : G) * u * (a : G)⁻¹,
    (mem_normalizer_iff.mp (c.normalized a.property) u).mp u.property⟩
  have he : c.coordinates v = c.coordinates u ↔
      τ a (c.coordinates u).toAdd = (c.coordinates u).toAdd := by
    rw [← Multiplicative.toAdd.injective.eq_iff, c.equivariant]
  have hz : c.coordinates v = c.coordinates u ↔ ⁅(a : G),(u : G)⁆ ∈ Z := by
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, c.coordinates_eq_one_iff]
    rfl
  rw [← he, hz]
  exact ⟨fun h => by simpa only [commutatorElement_inv] using Z.inv_mem h,
    fun h => by simpa only [commutatorElement_inv] using Z.inv_mem h⟩

/-- Lift one fixed-moving coordinate through the exact section kernel. -/
theorem exists_fixed_moving_lift
    (c : BinaryConjugationSection H W Z τ) (K S : Subgroup G)
    (hSH : S ≤ H) (v : V)
    (hfixed : ∀ (s : G) (hs : s ∈ S), τ ⟨s,hSH hs⟩ v = v)
    (hmoved : v ∉ fixed (τ.comp (K.subgroupOf H).subtype)) :
    ∃ u ∈ W, (∀ s ∈ S, ⁅u,s⁆ ∈ Z) ∧ ∃ k ∈ K, ⁅u,k⁆ ∉ Z := by
  classical
  obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd v)
  have hu' : (c.coordinates u).toAdd = v := congrArg Multiplicative.toAdd hu
  refine ⟨u,u.property,?_,?_⟩
  · intro s hs
    apply (c.fixed_coordinate_iff_commutator_mem ⟨s,hSH hs⟩ u).mp
    rw [hu']
    exact hfixed s hs
  · by_contra hn
    push Not at hn
    apply hmoved
    intro k
    change τ k.val v = v
    rw [← hu']
    exact (c.fixed_coordinate_iff_commutator_mem k.val u).mpr (hn k.val k.property)
end Representation.BinaryConjugationSection
