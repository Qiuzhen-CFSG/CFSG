module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Prime-order conjugation and fixed points

An element of prime order has a conjugate in every subgroup of index
coprime to that prime: its cyclic group fixes a coset. Similarly, a
prime-order element normalizing a finite subgroup fixes a nonidentity
element whenever the prime does not divide the subgroup order minus one.
Both assertions are applications of the fixed-point congruence for p-groups.

These are used in the literal stabilizer argument of GLS, Volume 4,
Chapter 2, Lemma 12.14(a).
-/

open Subgroup

namespace Theory.GroupAction

/-- A prime-order element fixes a coset of every subgroup of coprime index. -/
public theorem exists_conjugate_mem_of_prime_order {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) {x : G} {p : ℕ} (hp : p.Prime) (hx : orderOf x = p)
    (hi : ¬ p ∣ H.index) : ∃ g : G, g⁻¹ * x * g ∈ H := by
  let : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨a, ha⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ H) hi
  obtain ⟨g, rfl⟩ := Quotient.mk_surjective a
  refine ⟨g, ?_⟩
  have hf := MulAction.mem_fixedPoints.mp ha (⟨x, mem_zpowers x⟩ : zpowers x)
  change x • (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk g at hf
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hf
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using H.inv_mem hf

/-- Conjugation on the nonidentity elements forces a nonidentity fixed element. -/
public theorem exists_commuting_nonidentity_of_prime_order
    {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    {x : G} {p : ℕ} (hp : p.Prime) (hx : orderOf x = p)
    (hxN : x ∈ normalizer (A : Set G)) (hcard : ¬ p ∣ Nat.card A - 1) :
    ∃ a ∈ A, a ≠ 1 ∧ Commute x a := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let P := zpowers x
  let rho : P →* MulAut A := A.normalizerMonoidHom.comp
    (inclusion (zpowers_le.mpr hxN))
  let : MulDistribMulAction P A := MulDistribMulAction.compHom A rho
  let X : SubMulAction P A :=
    { carrier := {a | a ≠ 1}
      smul_mem' := by
        intro g a ha he
        apply ha
        exact (MulAction.injective g) (he.trans (smul_one g).symm) }
  have hc : Nat.card X = Nat.card A - 1 := by
    let := Fintype.ofFinite A
    change Nat.card {a : A // ¬ a = 1} = _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp only [Fintype.card_unique, Nat.card_eq_fintype_card]
  have hP : IsPGroup p P := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨a, ha⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card X (by rwa [hc])
  refine ⟨a.val, a.val.property, fun h => a.property (Subtype.ext h), ?_⟩
  have he := congrArg (fun b : X => ((b : A) : G))
    (MulAction.mem_fixedPoints.mp ha (⟨x, mem_zpowers x⟩ : P))
  change x * (a.val : G) * x⁻¹ = (a.val : G) at he
  exact mul_inv_eq_iff_eq_mul.mp he

end Theory.GroupAction
