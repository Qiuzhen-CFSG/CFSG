module
public import Theory.Representation.SL2.PerfectCoreQuotientDegree
public import Theory.GroupAction.PerfectFrattiniAction
public import Theory.Representation.FrattiniAction
public import Theory.GroupAction.SubgroupQuotientCommutatorBound
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Cardinal bounds for two-groups with perfect rank-one action

A nontrivial perfect action on a finite two-group survives on its Frattini
quotient. The binary degree bound for an actor with quotient SL₂(F) then
forces at least |F|² elements. Applied to literal quotient conjugation, this
bounds every proper invariant quotient of a fully moved two-subgroup.

Source application: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs*
(1985), (5.7) and the proper-quotient step of (10.10)(d), printed p.165.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups commutatorElement

namespace Representation.SL2

/-- A nontrivial perfect rank-one action forces the natural cardinal bound. -/
theorem twoGroup_card_lower_of_action_ne_one
    {H F T : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Field F] [Finite F] [CharP F 2] [Group T] [Finite T]
    (e : (H ⧸ pCore 2 H) ≃* SL(2,F))
    (hp : IsPGroup 2 T) (a : H →* MulAut T) (ha : a ≠ 1) :
    Nat.card F ^ 2 ≤ Nat.card T := by
  let : Fact (IsPGroup 2 T) := ⟨hp⟩
  let V := T ⧸ frattini T
  let : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini
  let : CommGroup V := IsMulCommutative.instCommGroup
  let b := (quotientAut (frattini T)).comp a
  have hb : b ≠ 1 := a.frattini_comp_ne_one_of_isPerfect hp ha
  obtain ⟨x,hx⟩ : ∃ x, b x ≠ 1 := by
    by_contra! hh
    exact hb (MonoidHom.ext hh)
  let ρ := FrattiniAction.ofAutomorphismHom b
  have hρ : ∃ x, ρ x ≠ 1 := by
    by_contra! hh
    exact FrattiniAction.ofAutomorphismHom_ne_one b x hx (MonoidHom.ext hh)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let n := Module.finrank (ZMod 2) F
  have hF : Nat.card F = 2^n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hn : n ≠ 0 := by
    intro hz
    have htwo : 1 < Nat.card F := Finite.one_lt_card
    rw [hF,hz,pow_zero] at htwo
    omega
  have hd := perfect_core_quotient_finrank_bound (V := Additive V) e ρ hρ hn hF
  have hV : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    change Nat.card (Additive V) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hl : Nat.card F^2 ≤ Nat.card V := by
    rw [hF,←pow_mul,hV]
    exact Nat.pow_le_pow_right (by decide) (by simpa only [Nat.mul_comm] using hd)
  exact hl.trans (Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card (frattini T)))

/-- Every proper invariant quotient of a fully moved two-group has order at least |F|². -/
theorem quotient_card_lower_of_full_commutator
    {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
    (A Q N : Subgroup G) [Finite A] [Finite Q] [Group.IsPerfect A]
    (e : (A ⧸ pCore 2 A) ≃* SL(2,F))
    (hp : IsPGroup 2 Q) (hNQ : N < Q)
    (hAQ : A ≤ normalizer (Q : Set G))
    (hAN : A ≤ normalizer (N : Set G))
    [(N.subgroupOf Q).Normal] (hfull : ⁅Q,A⁆ = Q) :
    Nat.card F^2 ≤ Nat.card (Q ⧸ N.subgroupOf Q) := by
  obtain ⟨a,ha⟩ := exists_quotient_conjugation_action A Q N hAQ hAN inferInstance
  have hne : a ≠ 1 := by
    intro hzero
    have hbound := quotient_conjugation_commutator_le_sup A Q N Q A ⊥ hAQ le_rfl le_rfl
      a ha (by intro actor _ point _; simp [hzero])
    rw [commutator_comm,hfull,bot_sup_eq] at hbound
    exact (not_le_of_gt hNQ) hbound
  exact twoGroup_card_lower_of_action_ne_one e
    (hp.of_surjective _ (QuotientGroup.mk'_surjective _)) a hne

/-- A small invariant section over a fixed central layer is centralized by the actor. -/
theorem centralizes_of_quotient_card_lt
    {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
    (A N Z : Subgroup G) [Finite A] [Finite N] [Group.IsPerfect A]
    (e : (A ⧸ pCore 2 A) ≃* SL(2,F)) (hp : IsPGroup 2 N)
    (hAN : A ≤ normalizer (N : Set G))
    (hZA : Z ≤ centralizer (A : Set G)) [(Z.subgroupOf N).Normal]
    (hsmall : Nat.card (N ⧸ Z.subgroupOf N) < Nat.card F^2) :
    N ≤ centralizer (A : Set G) := by
  obtain ⟨a,ha⟩ := exists_quotient_conjugation_action A N Z hAN
    ((le_centralizer_iff.mp hZA).trans (Subgroup.centralizer_le_normalizer _)) inferInstance
  have hz : a = 1 := by
    by_contra hne
    exact (not_le_of_gt hsmall) (twoGroup_card_lower_of_action_ne_one e
      (hp.of_surjective _ (QuotientGroup.mk'_surjective _)) a hne)
  have hbound := quotient_conjugation_commutator_le_sup A N Z N A ⊥ hAN le_rfl le_rfl
    a ha (by intro actor _ point _; simp [hz])
  rw [commutator_comm,bot_sup_eq] at hbound
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_eq_bot_of_iterated_eq_bot
  exact bot_unique ((commutator_mono hbound le_rfl).trans
    (commutator_eq_bot_iff_le_centralizer.mpr hZA).le)

end Representation.SL2
