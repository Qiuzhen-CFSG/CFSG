module

public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime residuals through abelian quotients with coprime kernels

A finite abelian group's p-residual has order prime to p. Apply the power
homomorphism for the prime-to-p part of its order: its image is a p-group,
so the residual lies in its kernel. Cauchy's theorem excludes p-torsion
there. A homomorphism with prime-to-p kernel transfers this conclusion
back to the domain. Surjections onto prime-to-p groups also show that their
orders divide the domain's p-residual order.

These elementary residual calculations support the lifted Borel arithmetic
in Aschbacher–Smith, proof of 13.8.20, printed pp.954–955.
-/

public section
namespace Subgroup

/-- A finite abelian group has a prime-to-p p-residual. -/
theorem coprime_card_pResidual_of_commGroup {A : Type*} [CommGroup A] [Finite A]
    (p : ℕ) [Fact p.Prime] : Nat.Coprime p (Nat.card (pResidual p A)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, m, hm, hcard⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.card_pos.ne' : Nat.card A ≠ 0) p hp.ne_one
  let f : A →* A := powMonoidHom m
  have hr : IsPGroup p f.range := by
    rintro ⟨_, x, rfl⟩
    refine ⟨n, Subtype.ext ?_⟩
    change (x ^ m) ^ (p ^ n) = 1
    rw [← pow_mul, Nat.mul_comm m, ← hcard, pow_card_eq_one']
  have hR : pResidual p A ≤ f.ker :=
    sInf_le ⟨inferInstance, hr.of_equiv (QuotientGroup.quotientKerEquivRange f).symm⟩
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := pResidual p A) p hd
  have hpow : x ^ m = 1 := Subtype.ext (hR x.property)
  exact hm (hx ▸ orderOf_dvd_of_pow_eq_one hpow)

/-- Coprime kernels preserve the absence of p-torsion in residuals. -/
theorem coprime_card_pResidual_of_abelian_coprime_kernel {D A : Type*}
    [Group D] [Finite D] [CommGroup A] [Finite A]
    (p : ℕ) [Fact p.Prime] (f : D →* A)
    (hk : Nat.Coprime p (Nat.card f.ker)) :
    Nat.Coprime p (Nat.card (pResidual p D)) := by
  have hp : p.Prime := Fact.out
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := pResidual p D) p hd
  let y : pResidual p A := ⟨f x, map_pResidual_le p f (mem_map.mpr ⟨x, x.property, rfl⟩)⟩
  have hypow : y ^ p = 1 := by
    apply Subtype.ext
    change (f x.val) ^ p = 1
    rw [← map_pow]
    have hxp : x ^ p = 1 := by simpa only [hx] using pow_orderOf_eq_one x
    rw [← Subgroup.coe_pow, hxp, Subgroup.coe_one, map_one]
  have hy : y = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (coprime_card_pResidual_of_commGroup (A := A) p)
      (orderOf_dvd_of_pow_eq_one hypow) (_root_.orderOf_dvd_natCard y))
  let z : f.ker := ⟨x.val, congrArg Subtype.val hy⟩
  have hz : orderOf z = p := by
    rw [← Subgroup.orderOf_coe z]
    exact (Subgroup.orderOf_coe x).trans hx
  exact hp.coprime_iff_not_dvd.mp hk (hz ▸ _root_.orderOf_dvd_natCard z)

/-- The order of a prime-to-p quotient divides the order of the p-residual. -/
theorem card_dvd_card_pResidual_of_surjective_coprime {D A : Type*}
    [Group D] [Finite D] [Group A] [Finite A] (p : ℕ)
    (f : D →* A) (hf : Function.Surjective f)
    (hA : Nat.Coprime p (Nat.card A)) : Nat.card A ∣ Nat.card (pResidual p D) := by
  have hR : pResidual p A = ⊤ := by
    apply top_unique
    intro a _
    exact mem_pResidual_of_orderOf_coprime (hA.of_dvd_right (_root_.orderOf_dvd_natCard a))
  have hr : (f.comp (pResidual p D).subtype).range = ⊤ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, map_pResidual_of_surjective p f hf, hR]
  exact card_dvd_of_surjective _ (MonoidHom.range_eq_top.mp hr)

end Subgroup
