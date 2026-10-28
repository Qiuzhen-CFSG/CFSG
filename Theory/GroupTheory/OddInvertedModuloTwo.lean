module
public import Mathlib.GroupTheory.PGroup

/-!
# Odd subgroups inverted modulo a two-group

If an odd subgroup E normalizes K and an element of K inverts E modulo a
 two-group P, then E lies in K. In N(K)/K, the square of each element of
 the image of E lies in the image of P. Coprimality kills these squares,
 and odd order kills the image of E itself. Neither P-normality nor
 normalization of E by the inverter is required.

This is the elementary quotient argument used in Aschbacher--Smith,
5.1.13, printed p.638, refs/quasithin.pdf.
-/

public noncomputable section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Inversion modulo a two-group places an odd subgroup in the subgroup
containing its inverter, provided it normalizes that subgroup. -/
theorem odd_inverted_mod_two_le {E P K : Subgroup G} (ho : Odd (Nat.card E))
    (hEN : E ≤ normalizer (K : Set G))
    (hP : IsPGroup 2 P) {t : G} (ht : t ∈ K)
    (hi : ∀ x ∈ E, t*x*t⁻¹*x ∈ P) : E ≤ K := by
  let N := normalizer (K : Set G)
  let R := K.subgroupOf N
  let : R.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let q := QuotientGroup.mk' R
  let Ebar := (E.subgroupOf N).map q
  let Pbar := (P.subgroupOf N).map q
  have he : Nat.card (E.subgroupOf N) = Nat.card E :=
    Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv
  have heo : Odd (Nat.card Ebar) := (he.symm ▸ ho).of_dvd_nat
    ((E.subgroupOf N).card_map_dvd q)
  have hp : IsPGroup 2 Pbar := hP.comap_subtype.map q
  have hdis : Disjoint Ebar Pbar := by
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact heo.coprime_two_right.pow_right k
  let tN : N := ⟨t,K.le_normalizer ht⟩
  have htq : q tN = 1 := (QuotientGroup.eq_one_iff tN).mpr ht
  intro x hx
  let xN : N := ⟨x,hEN hx⟩
  have hxe : q xN ∈ Ebar := mem_map_of_mem q hx
  have hs : q xN ^ 2 ∈ Pbar := by
    have hh := mem_map_of_mem q (show tN*xN*tN⁻¹*xN ∈ P.subgroupOf N from hi x hx)
    simpa only [map_mul,map_inv,htq,one_mul,inv_one,mul_one,pow_two] using hh
  have hsq : q xN ^ 2 = 1 := mem_bot.mp (hdis.le_bot ⟨Ebar.pow_mem hxe 2,hs⟩)
  have hval : (⟨q xN,hxe⟩ : Ebar) = 1 :=
    (Nat.Coprime.pow_left_bijective (G := Ebar) heo.coprime_two_right).injective
      (by apply Subtype.ext; change q xN ^ 2 = 1 ^ 2; simpa only [one_pow] using hsq)
  exact (QuotientGroup.eq_one_iff xN).mp (congrArg Subtype.val hval)

end Theory.GroupTheory
