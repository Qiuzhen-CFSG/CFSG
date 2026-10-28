module
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal
public import Theory.GroupTheory.PrimeCyclicCoverage
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# From an odd centralizer to a prime-normalizer bound in J₁

Sylow conjugacy transports the absence of commuting involutions from one
prime-order element to every subgroup of that order. Thus its centralizer
has odd order. The conjugation map from the normalizer into the automorphism
group of the cyclic subgroup has precisely this centralizer as kernel; its
image order divides p−1. This justifies the normalizer action needed for the
large-prime entries of GLS3 Table 5.3f, used on Aschbacher–Smith p.510.
-/

namespace Janko1.LocalStructure.LargePrimes
open Subgroup

/-- Absence of commuting involutions for one representative forces the bound
for every subgroup of the same prime order. -/
public theorem bound_of_no_commuting_involution {p : ℕ} (hp : p.Prime)
    (hsq : ¬ p ^ 2 ∣ Nat.card Model) (hAut : ¬ 8 ∣ p - 1)
    (r : Model) (hr : orderOf r = p)
    (hno : ∀ t : Model, orderOf t = 2 → ¬ Commute t r) :
    PrimeNormalizerBound p := by
  let : Fact p.Prime := ⟨hp⟩
  intro A hA
  have hC : ¬ 2 ∣ Nat.card (centralizer (A : Set Model)) := by
    intro htwo
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
      (G := centralizer (A : Set Model)) 2 htwo
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) p (hA ▸ dvd_rfl)
    have hx' : orderOf (x : Model) = p := by
      simpa only [Subgroup.orderOf_coe] using hx
    obtain ⟨k, g, hg⟩ :=
      PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd hp hsq hx' hr
    have htx : Commute (t : Model) (x : Model) :=
      (mem_centralizer_iff.mp t.property x x.property).symm
    have ht' : orderOf (g * (t : Model) * g⁻¹) = 2 := by
      change orderOf (MulAut.conj g (t : Model)) = 2
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, ht]
    apply hno _ ht'
    rw [hg]
    exact (htx.pow_right k).map (MulAut.conj g)
  let : IsCyclic A := isCyclic_of_prime_card hA
  let f := A.normalizerMonoidHom
  have hk : Nat.card f.ker = Nat.card (centralizer (A : Set Model)) := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set Model))).toEquiv]
  have hcop : Nat.Coprime 8 (Nat.card f.ker) := by
    have hc := (Nat.prime_two.coprime_iff_not_dvd.mpr (hk ▸ hC)).pow_left 3
    exact hc
  have hprod := f.ker.card_mul_index
  rw [index_ker] at hprod
  intro hdiv
  have hrange : 8 ∣ Nat.card f.range := hcop.dvd_mul_left.mp (hprod ▸ hdiv)
  apply hAut
  have h := hrange.trans f.range.card_subgroup_dvd_card
  rwa [IsCyclic.card_mulAut, hA, Nat.totient_prime hp] at h

end Janko1.LocalStructure.LargePrimes
