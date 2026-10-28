module
public import Theory.GroupTheory.SelfCentralizingFourSymmetricFour
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Mathlib.GroupTheory.Sylow

/-!
# Symmetric four-normalizers from a cubic automizer

A self-centralizing four-group has normalizer order at most 24. When eight
divides the ambient group order, the Sylow normalizer congruence makes eight
divide its normalizer order as well. A cubic automizer supplies the remaining
factor of three. The order-24 recognition theorem then identifies the full
normalizer with S₄.

This is the subgroup-theoretic step used with the explicit PSL₂ matrices in
Aschbacher–Smith 2.5.8(5), printed pp.556–557.
-/

open Subgroup
namespace Theory.GroupTheory

/-- A cubic automizer and a larger ambient two-part force the full normalizer S₄. -/
public theorem four_normalizer_equiv_of_cubic
    {G : Type*} [Group G] [Finite G] (F : Subgroup G) [IsKleinFour F]
    (hself : centralizer (F : Set G) = F)
    (h8 : 8 ∣ Nat.card G) (h3 : 3 ∣ Nat.card (normalizer (F : Set G))) :
    Nonempty (normalizer (F : Set G) ≃* Equiv.Perm (Fin 4)) := by
  have hk : Nat.card F.normalizerMonoidHom.ker = 4 := by
    rw [F.normalizerMonoidHom_ker, hself,
      Nat.card_congr (subgroupOfEquivOfLe F.le_normalizer).toEquiv, IsKleinFour.card_four]
  have hr : Nat.card F.normalizerMonoidHom.range ≤ 6 := by
    simpa only [IsKleinFour.card_mulAut] using
      Nat.card_le_card_of_injective F.normalizerMonoidHom.range.subtype Subtype.val_injective
  have hh := F.normalizerMonoidHom.ker.card_mul_index
  rw [index_ker, hk] at hh
  have hbound : Nat.card (normalizer (F : Set G)) ≤ 24 := by omega
  have h8N : 8 ∣ Nat.card (normalizer (F : Set G)) :=
    Sylow.prime_pow_dvd_card_normalizer (p := 2) (n := 2) h8 IsKleinFour.card_four
  have h24 : 24 ∣ Nat.card (normalizer (F : Set G)) :=
    (by decide : Nat.Coprime 8 3).mul_dvd_of_dvd_of_dvd h8N h3
  have hN : Nat.card (normalizer (F : Set G)) = 24 :=
    Nat.le_antisymm hbound (Nat.le_of_dvd Nat.card_pos h24)
  let N := normalizer (F : Set G)
  let U := F.subgroupOf N
  let : IsElementaryAbelian 2 F :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by simp }
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf F.le_normalizer
  have hU : Nat.card U = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe F.le_normalizer).toEquiv).trans IsKleinFour.card_four
  apply mulEquiv_perm_four_of_selfCentralizing_four_card_twentyfour U hU _ hN
  intro x hx
  change (x : G) ∈ F
  rw [← hself]
  intro f hf
  exact congrArg Subtype.val (hx ⟨f, F.le_normalizer hf⟩ hf)

end Theory.GroupTheory
