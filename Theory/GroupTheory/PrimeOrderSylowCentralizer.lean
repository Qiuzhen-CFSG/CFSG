module
public import Theory.GroupTheory.SylowElementConjugacy
public import Mathlib.Tactic.Linarith

/-!
# Mixed element orders and self-centralizing Sylow subgroups

If a Sylow subgroup has prime order and is self-centralizing, no element
has order a proper multiple of that prime. Conjugate the prime-order power
into the chosen Sylow subgroup; it generates that subgroup, so the whole
element centralizes it and must lie in it.

This elementary consequence of Sylow conjugacy supplies the absence of
mixed element orders in Brauer--Tuan, *On simple groups of finite order I*,
Lemma 3.
-/

namespace Sylow
open Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

/-- Self-centralization excludes proper multiples of the prime as element orders. -/
public theorem orderOf_ne_prime_mul_of_self_centralizing
    (P : Sylow p G) (hP : Nat.card P = p)
    (hC : centralizer (P : Set G) = (P : Subgroup G))
    {q : ℕ} (hq : 1 < q) (x : G) : orderOf x ≠ p * q := by
  intro hx
  have hxq : orderOf (x ^ q) = p ^ 1 := by
    rw [orderOf_pow_of_dvd (by omega) (hx ▸ dvd_mul_left q p), hx,
      Nat.mul_div_cancel _ (by omega), pow_one]
  obtain ⟨y, hy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow hxq
  obtain ⟨g, hg⟩ := isConj_iff.mp hy
  change (MulAut.conj g) (x ^ q) = (y : G) at hg
  let z := (MulAut.conj g) x
  have hzy : z ^ q = (y : G) := by
    simpa only [z, ← map_pow] using hg
  have hyorder : orderOf (y : G) = p := by
    rw [← hg, (MulAut.conj g).orderOf_eq]
    simpa using hxq
  have hygen : zpowers (y : G) = (P : Subgroup G) :=
    eq_of_le_of_card_ge (zpowers_le.mpr y.property)
      (by rw [Nat.card_zpowers, hyorder]; exact hP.le)
  have hle : (P : Subgroup G) ≤ centralizer ({z} : Set G) := by
    rw [← hygen]
    apply zpowers_le.mpr
    apply mem_centralizer_singleton_iff.mpr
    rw [← hzy]
    exact (Commute.self_pow z q).symm.eq
  have hz : z ∈ P := by
    change z ∈ (P : Subgroup G)
    rw [← hC]
    exact mem_centralizer_iff.mpr fun a ha => mem_centralizer_singleton_iff.mp (hle ha)
  have hdiv : orderOf z ∣ p := by
    simpa only [hP, Subgroup.orderOf_mk] using
      (orderOf_dvd_natCard (⟨z, hz⟩ : (P : Subgroup G)))
  have hzorder : orderOf z = p * q := (MulAut.conj g).orderOf_eq x |>.trans hx
  rw [hzorder] at hdiv
  have hle' := Nat.le_of_dvd hp.out.pos hdiv
  have hp' := hp.out.pos
  nlinarith

end Sylow
