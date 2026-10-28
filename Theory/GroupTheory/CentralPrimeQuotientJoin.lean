module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# A central prime-order image from generating subgroups

Let A, B, and C generate a finite group. If the image of C under a
homomorphism has prime order and commutes with the images of A and B, it is
central in the entire image. Any nonidentity image has a representative in C
whose prime power and all commutators lie in the kernel. No splitting or
prime-order representative in the original group is asserted.

This is the central-coset step in Aschbacher, *Sporadic Groups* (1994),
8.15(5), specialized to a cubic quotient in 46.3, pp.29–30 and 251.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]
theorem exists_central_prime_coset_of_generators (f : G →* H) (A B C : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hgen : A ⊔ B ⊔ C = ⊤) (hc : Nat.card (C.map f) = p)
    (ha : ⁅A, C⁆ ≤ f.ker) (hb : ⁅B, C⁆ ≤ f.ker) :
    ∃ c : G, c ∈ C ∧ c ∉ f.ker ∧ c ^ p ∈ f.ker ∧ ∀ g : G, ⁅c, g⁆ ∈ f.ker := by
  let D := C.map f
  let : Finite D := Nat.finite_of_card_ne_zero (by
    rw [show Nat.card D = p from hc]
    exact (Fact.out : p.Prime).ne_zero)
  let : IsCyclic D := isCyclic_of_prime_card hc
  have hself : D ≤ centralizer (D : Set H) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hA : A.map f ≤ centralizer (D : Set H) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    exact (map_eq_bot_iff _).mpr ha
  have hB : B.map f ≤ centralizer (D : Set H) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    exact (map_eq_bot_iff _).mpr hb
  have hfull : f.range ≤ centralizer (D : Set H) := by
    rw [MonoidHom.range_eq_map, ← hgen, map_sup, map_sup]
    exact sup_le (sup_le hA hB) hself
  let : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (hc ▸ (Fact.out : p.Prime).one_lt)
  obtain ⟨d, hd⟩ := exists_ne (1 : D)
  obtain ⟨c, hcC, he⟩ := d.property
  refine ⟨c, hcC, ?_, ?_, ?_⟩
  · intro h
    apply hd
    apply Subtype.ext
    exact he.symm.trans h
  · change f (c ^ p) = 1
    rw [map_pow, he]
    have hp := pow_card_eq_one' (x := d)
    rw [hc] at hp
    exact congrArg Subtype.val hp
  · intro g
    change f ⁅c, g⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hfull ⟨g, rfl⟩ (f c) (mem_map_of_mem f hcC)
end Subgroup
