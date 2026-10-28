module

public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Involutions normalizing prime-order subgroups

An automorphism of a prime-order group either is the identity or fixes only
its identity element. A fixed-point-free automorphism whose square is the
identity acts by inversion. Applying this to conjugation gives the dichotomy
used in Aschbacher--Smith, *The Classification of Quasithin Groups*, D.2.12(3),
`refs/quasithin.pdf`, printed pp.183–184.
-/

/-- An element with square one that normalizes a prime-order subgroup
centralizes it or inverts every element of it. -/
public theorem centralizes_or_inverts_prime_subgroup_of_sq_eq_one {G : Type*} [Group G] [Finite G]
    (X : Subgroup G) (hp : (Nat.card X).Prime) (t : G) (ht : t ^ 2 = 1)
    (hn : t ∈ Subgroup.normalizer (X : Set G)) :
    (∀ x ∈ X, Commute t x) ∨ (∀ x ∈ X, t * x * t⁻¹ = x⁻¹) := by
  let _ : Fact (Nat.card X).Prime := ⟨hp⟩
  let tn : Subgroup.normalizer (X : Set G) := ⟨t, hn⟩
  let φ : MulAut X := X.normalizerMonoidHom tn
  by_cases he : φ = 1
  · left
    intro x hx
    have hh := congrArg Subtype.val (congrArg (fun f : MulAut X => f ⟨x, hx⟩) he)
    change t * x * t⁻¹ = x at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · right
    have hfree : MonoidHom.FixedPointFree φ := by
      intro x hx
      by_contra hxne
      apply he
      ext y
      obtain ⟨z, rfl⟩ := (Subgroup.mem_zpowers_iff).mp
        (mem_zpowers_of_prime_card (rfl : Nat.card X = Nat.card X) hxne :
          y ∈ Subgroup.zpowers x)
      rw [map_zpow, hx]
      rfl
    have hs : φ ^ 2 = 1 := by
      change X.normalizerMonoidHom tn ^ 2 = 1
      rw [← map_pow, show tn ^ 2 = 1 from Subtype.ext ht, map_one]
    have hi : Function.Involutive φ := fun x => congrArg (fun f : MulAut X => f x) hs
    intro x hx
    exact congrArg Subtype.val (congrFun (hfree.coe_eq_inv_of_involutive hi) ⟨x, hx⟩)

