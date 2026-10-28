module
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Prime coefficient representatives in an automorphism overgroup

If coefficient automorphisms inject into the outer quotient and inner
and coefficient automorphisms cover the full automorphism group, an
outer order-p element has a coefficient factor of the same prime order.
Cancel its inner factor inside the original overgroup to retain actual
membership. No conjugacy or fixed-group classification is assumed.

The triality and Ree applications in NonblockEndgameSieveModelsFieldActors
use their proved coefficient separation and coverage on actual models.
Source: Aschbacher–Smith A.3.18, printed pp.51–53; GLS3 Theorem 2.5.12.
-/

public section
open Subgroup
namespace MulAut
variable {M C : Type*} [Group M] [Group C]

/-- An outer prime actor can be stripped of its inner factor inside the same overgroup. -/
theorem exists_prime_coefficient_in_overgroup
    (φ : C →* MulAut M)
    (hfaithful : Function.Injective ((QuotientGroup.mk' (innerSubgroup M)).comp φ))
    (hcover : ∀ a : MulAut M, ∃ g : M, ∃ c : C, a = conj g * φ c)
    (A : Subgroup (MulAut M)) (hinner : innerSubgroup M ≤ A)
    {p : ℕ} [Fact p.Prime] (a : MulAut M) (ha : a ∈ A)
    (hp : orderOf a = p) (hout : a ∉ innerSubgroup M) :
    ∃ (g : M) (c : C), a = conj g * φ c ∧ orderOf c = p ∧
      φ c ∈ A ∧ orderOf (φ c) = p ∧ φ c ∉ innerSubgroup M := by
  let q := QuotientGroup.mk' (innerSubgroup M)
  obtain ⟨g,c,he⟩ := hcover a
  have hq : q a = q (φ c) := by
    rw [he,map_mul,show q (conj g)=1 from (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩,one_mul]
  have hcp : c^p=1 := by
    apply hfaithful
    change q (φ (c^p)) = q (φ 1)
    rw [map_pow,map_pow,←hq,←map_pow,←hp,pow_orderOf_eq_one,map_one,map_one,map_one]
  have houter : φ c ∉ innerSubgroup M := by
    intro hi
    exact hout ((QuotientGroup.eq_one_iff _).mp
      (hq.trans ((QuotientGroup.eq_one_iff _).mpr hi)))
  have hc : orderOf c=p := orderOf_eq_prime hcp (by
    intro hc
    apply houter
    rw [hc,map_one]
    exact (innerSubgroup M).one_mem)
  have hcA : φ c ∈ A := by
    have hh := A.mul_mem (A.inv_mem (hinner ⟨g,rfl⟩)) ha
    rwa [he,inv_mul_cancel_left] at hh
  refine ⟨g,c,he,hc,hcA,?_,houter⟩
  apply orderOf_eq_prime
  · rw [←map_pow,hcp,map_one]
  · exact fun hh => houter (hh ▸ (innerSubgroup M).one_mem)
end MulAut
