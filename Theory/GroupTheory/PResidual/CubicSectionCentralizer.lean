module

public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PResidual.SmallCubicNormal

/-!
# Centralizers in sections with a small two-residual

Suppose the two-residual has order dividing twelve. If a normal two-subgroup
meets it nontrivially, the residual in the quotient has order dividing six,
so the quotient has a normal Sylow three-subgroup. Consequently a nonnormal
Sylow three-subgroup in the quotient forces the two-residual, and hence every
cubic subgroup, to centralize the original normal two-subgroup.

Source application: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(5.3), printed p.395. The local residual classification supplies the order
bound in the maximal local normalizer; subgroup functoriality passes it to
the actual track normalizer.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A nonnormal Sylow three-subgroup in the quotient forces the original
two-residual to centralize the normal two-subgroup. -/
theorem residual_le_centralizer_of_nonNormal_three_quotient
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hR : Nat.card (pResidual 2 G) ∣ 12)
    (P : Sylow 3 (G ⧸ N)) (hP : ¬ (P : Subgroup (G ⧸ N)).Normal) :
    pResidual 2 G ≤ centralizer (N : Set G) := by
  let K := N.subgroupOf (pResidual 2 G)
  have hK : IsPGroup 2 K := hN.comap_subtype
  have hc : Nat.card (pResidual 2 (G ⧸ N)) * Nat.card K =
      Nat.card (pResidual 2 G) := by
    have he := Nat.card_congr (pResidualQuotientEquiv 2 N).toEquiv
    change K.index = Nat.card (pResidual 2 (G ⧸ N)) at he
    rw [← he]
    exact K.index_mul_card
  have hbot : K = ⊥ := by
    rcases hK.card_eq_or_dvd with he | hd
    · exact Subgroup.card_eq_one.mp he
    · apply False.elim
      apply hP
      apply P.normal_of_twoResidual_card_dvd_six
      have htwo : 2 * Nat.card (pResidual 2 (G ⧸ N)) ∣ 2 * 6 := by
        have hm := Nat.mul_dvd_mul_left (Nat.card (pResidual 2 (G ⧸ N))) hd
        rw [hc] at hm
        simpa only [Nat.mul_comm] using hm.trans hR
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp htwo
  have hdis : Disjoint (pResidual 2 G) N :=
    (Subgroup.subgroupOf_eq_bot.mp hbot).symm
  exact commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_disjoint hdis)

/-- The conclusion retains any supplied cubic subgroup of the original
group, without choosing a new Sylow marking. -/
theorem cubic_le_centralizer_of_nonNormal_three_quotient
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hR : Nat.card (pResidual 2 G) ∣ 12)
    (P : Sylow 3 (G ⧸ N)) (hP : ¬ (P : Subgroup (G ⧸ N)).Normal)
    (X : Subgroup G) (hX : Nat.card X = 3) : X ≤ centralizer (N : Set G) := by
  apply le_trans ?_ (residual_le_centralizer_of_nonNormal_three_quotient N hN hR P hP)
  intro x hx
  apply Subgroup.mem_pResidual_of_orderOf_coprime
  have ho : orderOf x ∣ 3 := by
    have hh := orderOf_dvd_natCard (⟨x, hx⟩ : X)
    simpa only [Subgroup.orderOf_mk, hX] using hh
  exact (show Nat.Coprime 2 3 by decide).of_dvd_right ho

end Theory.GroupTheory
