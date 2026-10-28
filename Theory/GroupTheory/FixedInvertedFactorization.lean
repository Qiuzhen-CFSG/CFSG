module
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Fixed and inverted factors for an involutive automorphism

An involutive automorphism of a finite group of odd order gives a unique
factorization of each element into a fixed factor followed by an inverted
factor. No commutativity hypothesis on the group is needed. The former abelian
statement remains available as a compatibility wrapper, preserving its public
name and argument order for the Brauer-plane development.

The noncommutative form is the fixed/inverted factorization invoked in
Gorenstein--Walter, *On finite groups with dihedral Sylow 2-subgroups*, Section
2, Lemma 4(i), via Gorenstein--Herstein Lemma 1. The abelian specialization is
the square-root reduction in Brauer, *On finite Desarguesian planes I*, equation
(2.4), article page 119.

Odd order makes squaring bijective. For an element `x`, choose the unique `t`
with `t ^ 2 = x⁻¹ * φ x`. Applying `φ` and using involutivity shows that
`φ t` and `t⁻¹` have the same square, hence are equal. Thus `x * t` is fixed,
`t⁻¹` is inverted, and their product is `x`. In any other factorization
`x = a * b`, the square of `b⁻¹` is again `x⁻¹ * φ x`; square-root uniqueness
first determines `b` and then cancellation determines `a`.
-/

namespace Theory.GroupTheory

/-- Every element of a finite odd-order group has unique fixed and inverted
factors under an involutive automorphism. -/
public theorem existsUnique_fixed_inverted_mul_of_odd_card
    {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G))
    (φ : MulAut G) (hφ : Function.Involutive φ) (x : G) :
    ∃! p : G × G, φ p.1 = p.1 ∧ φ p.2 = p.2⁻¹ ∧ p.1 * p.2 = x := by
  have hsquare : Function.Bijective (fun g : G => g ^ 2) :=
    hodd.coprime_two_right.pow_left_bijective
  obtain ⟨t, ht⟩ := hsquare.surjective (x⁻¹ * φ x)
  change t ^ 2 = x⁻¹ * φ x at ht
  have htinv : φ t = t⁻¹ := by
    apply hsquare.injective
    change (φ t) ^ 2 = (t⁻¹) ^ 2
    rw [← map_pow, ht, map_mul, map_inv, hφ x, inv_pow, ht]
    simp
  let u : G := x * t
  let v : G := t⁻¹
  have hphix : φ x = x * (t * t) := by
    rw [← pow_two, ht]
    simp
  have hufix : φ u = u := by
    simp only [u, map_mul, htinv, hphix]
    simp [mul_assoc]
  have hvinv : φ v = v⁻¹ := by simp [v, htinv]
  have huv : u * v = x := by simp [u, v]
  refine ⟨(u, v), ⟨hufix, hvinv, huv⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
  have hbSquare : b⁻¹ ^ 2 = x⁻¹ * φ x := by
    rw [← hab, map_mul, ha, hb]
    simp [pow_two, mul_assoc]
  have hbt : b⁻¹ = t := hsquare.injective (hbSquare.trans ht.symm)
  have hbv : b = v := by
    simpa [v] using congrArg Inv.inv hbt
  have hau : a = u := by
    apply mul_right_cancel (b := b)
    rw [hab, hbv, huv]
  exact Prod.ext hau hbv

/-- Compatibility form of `existsUnique_fixed_inverted_mul_of_odd_card` for a
group supplied with an explicit pairwise-commutativity hypothesis. -/
public theorem existsUnique_fixed_inverted_mul
    {A : Type*} [Group A] [Finite A] (_ : ∀ a b : A, Commute a b)
    (hodd : Odd (Nat.card A)) (φ : MulAut A) (hφ : Function.Involutive φ) (x : A) :
    ∃! p : A × A, φ p.1 = p.1 ∧ φ p.2 = p.2⁻¹ ∧ p.1 * p.2 = x := by
  exact existsUnique_fixed_inverted_mul_of_odd_card hodd φ hφ x

end Theory.GroupTheory
