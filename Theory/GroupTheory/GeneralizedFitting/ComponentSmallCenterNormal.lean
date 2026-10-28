module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PrimeRankCentralizer

/-!
# Normality of rank-two components with small center

In ambient p-rank at most two, a rank-two subgroup contains every
centralizing element of exponent p. If a component had a distinct
conjugate, their commutation would therefore put an elementary plane
of the conjugate in its own center. A center of order less than p squared
excludes this and forces normality.

This handles the cubic-centered components in Aschbacher--Smith,
proof of 12.6.26, printed p.832, without discarding their central covers.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem IsComponent.normal_of_rank_two_small_center
    {B : Subgroup G} (hB : IsComponent G B) {p : ℕ} [Fact p.Prime]
    (hG : primeRank p G ≤ 2) (hr : primeRank p B = 2)
    (hc : Nat.card (center B) < p ^ 2) : B.Normal := by
  obtain ⟨E,hE,he⟩ := exists_elementaryAbelian_card_primeRank (G := B) (p := p)
  let := hE
  rw [hr] at he
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hn
  let f := MulAut.conj g
  have hcomm : B.map f.toMonoidHom ≤ centralizer (B : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp ((hB.map_conj g).commutator_eq_bot_of_ne hB hn)
  have hEC : E ≤ center B := by
    intro x hx
    have hxp : x ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
    have hfx : f (x : G) ∈ B := B.mem_of_prime_pow_eq_one_of_centralizes_rank_two hG hr
      (by rw [←map_pow,show (x : G)^p=1 from congrArg Subtype.val hxp,map_one])
      (hcomm (mem_map_of_mem f.toMonoidHom x.property))
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    apply f.injective
    simpa only [map_mul,coe_mul,MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe] using
      (hcomm (mem_map_of_mem f.toMonoidHom b.property) _ hfx).symm
  have hh := Nat.card_le_card_of_injective (inclusion hEC) (inclusion_injective hEC)
  rw [he] at hh
  omega
end Theory.GroupTheory
