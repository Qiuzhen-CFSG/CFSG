module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ResidualProduct

/-!
# Squares in the original cubic normalizer centralize its Sylow subgroup

Every nine-subgroup of H lies in O²(H). The residual is its product with
Q, and a Q-element normalizing this coprime subgroup centralizes it.
Since H-squares lie in the residual, the action of N_H(X) on X has
exponent two. This is the exact source input excluding the order-nine
odd-kernel alternative once the elementary-plane A₆ normalizer is built.

Source: Aschbacher, *Sporadic Groups* (1994),45.3(5),45.5(1),45.7, pp.243–245.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace CentralizerHypothesis
variable (h : CentralizerHypothesis z) (X : Subgroup G)
  (hX : Nat.card X=9) (hXH : X≤centralizer z)
include hX hXH in
omit [Finite G] in
theorem cubic_le_residual : X≤residual z := by
  intro x hx
  let xH : centralizer z := ⟨x,hXH hx⟩
  have hxorder : orderOf xH∣9 := by
    rw [←orderOf_coe xH]
    exact (orderOf_coe (⟨x,hx⟩:X)) ▸ (hX ▸ orderOf_dvd_natCard (⟨x,hx⟩:X))
  exact mem_map_of_mem (centralizer z).subtype
    (mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 9).of_dvd_right hxorder))

include h hX hXH in
theorem residual_eq_core_sup_cubic : residual z=core z⊔X := by
  have hXL : X≤residual z := cubic_le_residual X hX hXH
  have hQ : core z≤residual z := pCoreIn_le 2 _
  have hn : X≤normalizer (core z : Set G) := hXH.trans centralizer_normalizes_core
  have hd : Disjoint (core z) X := disjoint_of_coprime_natCard
    (by rw [h.core_card,hX]; decide)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (core z) X hn
  rw [h.core_card,hX,hd.eq_bot,card_bot] at hc
  simp only [one_mul] at hc
  symm
  apply eq_of_le_of_card_ge (sup_le hQ hXL)
  rw [h.residual_card,←hc]

include h hX hXH in
theorem residual_normalizer_centralizes_cubic :
    residual z⊓normalizer (X:Set G)≤Subgroup.centralizer (X:Set G) := by
  have hn : X≤normalizer (core z : Set G) := hXH.trans centralizer_normalizes_core
  have hd : Disjoint (core z) X := disjoint_of_coprime_natCard
    (by rw [h.core_card,hX]; decide)
  have hQNX : core z⊓normalizer (X:Set G)≤Subgroup.centralizer (X:Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [←hd.eq_bot]
    refine le_inf ?_ (le_normalizer_iff_commutator_le_right.mp inf_le_right)
    exact (commutator_mono inf_le_left le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hn)
  have hXC : X≤Subgroup.centralizer (X:Set G) := by
    let : IsMulCommutative X := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p:=3) hX
    intro x hx y hy
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M:=X)).comm ⟨y,hy⟩ ⟨x,hx⟩)
  intro n hnX
  have hp : n∈(core z:Set G)*(X:Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left (core z) X hn,←h.residual_eq_core_sup_cubic X hX hXH]
    exact hnX.1
  obtain ⟨q,hq,x,hx,rfl⟩ := hp
  have hqN : q∈normalizer (X:Set G) := by
    simpa only [mul_inv_cancel_right] using (normalizer (X:Set G)).mul_mem hnX.2
      ((normalizer (X:Set G)).inv_mem (X.le_normalizer hx))
  exact (Subgroup.centralizer (X:Set G)).mul_mem (hQNX ⟨hq,hqN⟩) (hXC hx)
end CentralizerHypothesis
namespace IsType
variable (h : IsType z)

include h in
/-- The original cubic normalizer acts with elementary binary quotient on X. -/
theorem cubic_normalizer_square_centralizes (X : Subgroup G)
    (hX : Nat.card X=9) (hXH : X≤centralizer z) (g : G)
    (hg : g∈normalizer (X:Set G)⊓centralizer z) :
    g^2∈Subgroup.centralizer (X:Set G) := by
  obtain ⟨P⟩ := h.exists_rootPair
  exact h.toCentralizerHypothesis.residual_normalizer_centralizes_cubic X hX hXH
    ⟨P.centralizer_square_mem_residual h g hg.2,
      (normalizer (X:Set G)).pow_mem hg.1 2⟩

end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
