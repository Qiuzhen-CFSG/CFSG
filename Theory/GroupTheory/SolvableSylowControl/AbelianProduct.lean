module
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.TwoGroupExclusion.Solvability
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.SolvableSylowControl
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Odd abelian products and normal-layer Sylow subgroups

A permuting odd abelian subgroup and a two-subgroup have solvable join:
the odd factor has two-power index in that actual join. If solvable Sylow
overgroups in a normal layer normalize their Sylow, the whole join then
normalizes its intersection with the supplied ambient Sylow. The layer
need not be centerless, and neither factor is assumed to normalize the other.

Source application: Aschbacher--Smith A.3.15(5) and 11.2.1,
printed pp.50--51,766--767, on the literal Cartan automizer witnesses.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Permutability and odd abelianness give solvability of the actual join. -/
theorem solvable_of_odd_abelian_permuting_two_subgroup
    (B U : Subgroup G) [IsMulCommutative B]
    (hB : Odd (Nat.card B)) (hU : IsPGroup 2 U)
    (hperm : (B : Set G) * U = (U : Set G) * B) :
    Group.IsSolvable (B ⊔ U : Subgroup G) := by
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  have hd : Disjoint B U := disjoint_of_coprime_natCard
    (by rw [hk]; exact hB.coprime_two_right.pow_right k)
  have hc := card_set_mul_mul_card_inf B U
  rw [hd.eq_bot, card_bot, mul_one, ← coe_sup_of_set_mul_comm B U hperm] at hc
  change Nat.card (B ⊔ U : Subgroup G) = Nat.card B * Nat.card U at hc
  let A := B ⊔ U
  have hindex : (B.subgroupOf A).index = 2 ^ k := by
    have h := (B.subgroupOf A).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show B ≤ A from le_sup_left)).toEquiv] at h
    change Nat.card B * (B.subgroupOf A).index = Nat.card (B ⊔ U : Subgroup G) at h
    rw [hc, hk] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  exact (B.subgroupOf A).isSolvable_of_isMulCommutative_of_prime_power_index
    Nat.prime_two hindex

/-- The whole permuting product normalizes the same Sylow intersection in a normal layer. -/
theorem odd_abelian_permuting_normalizes_layer_sylow
    (K B : Subgroup G) [K.Normal] [IsMulCommutative B]
    (T : Sylow 2 G) (hB : Odd (Nat.card B))
    (hperm : (B : Set G) * T = (T : Set G) * B)
    (hcontrol : SolvableSylowControl 2 K) :
    B ⊔ (T : Subgroup G) ≤ normalizer ((T : Subgroup G) ⊓ K : Set G) := by
  let A := B ⊔ (T : Subgroup G)
  let := solvable_of_odd_abelian_permuting_two_subgroup B T hB T.isPGroup' hperm
  obtain ⟨U,hU⟩ := T.exists_subgroupOf_eq_of_normal K
  have he : (U : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K := by
    rw [hU, subgroupOf_map_subtype]
  have hn := hcontrol.normalizes_sylow K A U (by simp [normalizer_eq_top])
    (show (U : Subgroup K).map K.subtype ≤ A by
      rw [he]; exact inf_le_left.trans le_sup_right)
  rwa [he] at hn
end Theory.GroupTheory
