module

public import Theory.GroupTheory.PGroup.CyclicFourSectionFixedPoints

/-!
# Derived lines from cyclic-four centralizer sections

Suppose a normal elementary four `W` lies properly in a normal subgroup `H`
of a finite two-group. A cyclic-four section with central kernel, containing
an involution `t`, cannot centralize `W` if all fixed points of `t` in `H`
lie in `W`. This is the normal-subgroup-chain obstruction.

If that section together with `W` generates the centralizer of `t`, its
derived subgroup is the central involution line in `W`. The section is
abelian because its cyclic quotient has central kernel. Commutators with
`W` lie in the central line because the remaining layer has order two;
noncentralization makes this commutator nontrivial.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, case (a), printed p.391.
-/

open Subgroup
namespace Subgroup

private theorem commutative_join_of_commuting
    {P : Type*} [Group P] (K W : Subgroup P)
    [IsMulCommutative K] [IsMulCommutative W]
    (hcomm : K ≤ centralizer (W : Set P)) : IsMulCommutative (K ⊔ W : Subgroup P) := by
  apply le_centralizer_iff_isMulCommutative.mp
  apply sup_le
  · exact le_centralizer_iff.mpr (sup_le K.le_centralizer (le_centralizer_iff.mp hcomm))
  · exact le_centralizer_iff.mpr (sup_le hcomm W.le_centralizer)

private theorem commutator_join_le_of_abelian_factors
    {P : Type*} [Group P] (K W Z : Subgroup P)
    [IsMulCommutative K] [IsMulCommutative W] [Z.Normal]
    (hcomm : ⁅K, W⁆ ≤ Z) : ⁅K ⊔ W, K ⊔ W⁆ ≤ Z := by
  let q := QuotientGroup.mk' Z
  have hcomm' : ⁅K.map q, W.map q⁆ = ⊥ := by
    rw [← map_commutator]
    exact (map_eq_bot_iff _).mpr (by simpa only [q, QuotientGroup.ker_mk'] using hcomm)
  let : IsMulCommutative (K.map q) := map_isMulCommutative K q
  let : IsMulCommutative (W.map q) := map_isMulCommutative W q
  let : IsMulCommutative (K.map q ⊔ W.map q : Subgroup (P ⧸ Z)) :=
    commutative_join_of_commuting _ _ (commutator_eq_bot_iff_le_centralizer.mp hcomm')
  have hmap : (⁅K ⊔ W, K ⊔ W⁆).map q = ⊥ := by
    rw [map_commutator, map_sup]
    exact commutator_self_eq_bot_iff.mpr inferInstance
  have hle := (map_eq_bot_iff _).mp hmap
  simpa only [q, QuotientGroup.ker_mk'] using hle

/-- The central involution bounds every commutator with a normal four. -/
public theorem normal_four_commutator_le_central_involution
    {P : Type*} [Group P] [Finite P]
    (W : Subgroup P) [W.Normal] (hW : Nat.card W = 4)
    (z : P) (hz : orderOf z = 2) (hzc : z ∈ center P) (hzW : z ∈ W) :
    ⁅(⊤ : Subgroup P), W⁆ ≤ zpowers z := by
  have hZW : zpowers z ≤ W := zpowers_le.mpr hzW
  have hZc : zpowers z ≤ center P := zpowers_le.mpr hzc
  let : (zpowers z).Normal := ⟨fun n hn g => by
    rw [(mem_center_iff.mp (hZc hn) g), mul_inv_cancel_right]
    exact hn⟩
  have hi : (zpowers z).relIndex W = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup P) (zpowers z) W bot_le hZW
    simp only [relIndex_bot_left, Nat.card_zpowers, hz, hW] at hh
    omega
  rw [commutator_comm]
  exact commutator_le_of_normalized_index_two W (zpowers z) ⊤ hZW hi
    le_normalizer_of_normal le_normalizer_of_normal

/-- The cyclic-four supplement and the fixed-core bound force the derived line. -/
public theorem centralizer_derived_eq_of_cyclic_four_section
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (W H : Subgroup P) [W.Normal] [H.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (hWH : W < H)
    (z : P) (hz : orderOf z = 2) (hzc : z ∈ center P) (hzW : z ∈ W)
    (K : Subgroup P)
    (Z : Subgroup K) [Z.Normal] [IsCyclic (K ⧸ Z)]
    (hquot : Nat.card (K ⧸ Z) = 4)
    (hZ : Z ≤ (center P).comap K.subtype)
    (t : K) (ht : t ^ 2 = 1)
    (hfixed : H ⊓ centralizer ({(t : P)} : Set P) ≤ W)
    (hgen : K ⊔ W = centralizer ({(t : P)} : Set P)) :
    (_root_.commutator (centralizer ({(t : P)} : Set P))).map
      (centralizer ({(t : P)} : Set P)).subtype = zpowers z := by
  let : IsMulCommutative K :=
    (QuotientGroup.mk' Z).isMulCommutative_of_isCyclic_of_ker_le_center (by
      rw [QuotientGroup.ker_mk']
      intro a ha
      exact mem_center_iff.mpr (fun k => Subtype.ext (mem_center_iff.mp (hZ ha) k)))
  have hnc : ¬ K ≤ centralizer (W : Set P) := by
    intro hK
    exact fixed_not_le_of_centralizing_cyclic_four_section hP W H hWH K Z hquot hZ hK t ht hfixed
  have hcomm : ⁅K, W⁆ ≤ zpowers z :=
    (commutator_mono le_top le_rfl).trans
      (normal_four_commutator_le_central_involution W hW z hz hzc hzW)
  have heq : ⁅K, W⁆ = zpowers z := by
    apply eq_of_le_of_card_ge hcomm
    have hne : ⁅K, W⁆ ≠ ⊥ := fun hh => hnc (commutator_eq_bot_iff_le_centralizer.mp hh)
    have hc : Nat.card (⁅K, W⁆ : Subgroup P) ≠ 1 := fun hh => hne (card_eq_one.mp hh)
    have hp : 0 < Nat.card (⁅K, W⁆ : Subgroup P) := Nat.card_pos
    rw [Nat.card_zpowers, hz]
    omega
  have hZc : zpowers z ≤ center P := zpowers_le.mpr hzc
  let : (zpowers z).Normal := ⟨fun n hn g => by
    rw [(mem_center_iff.mp (hZc hn) g), mul_inv_cancel_right]
    exact hn⟩
  rw [map_subtype_commutator, ← hgen]
  exact le_antisymm (commutator_join_le_of_abelian_factors K W (zpowers z) hcomm)
    (heq ▸ commutator_mono le_sup_left le_sup_right)

end Subgroup
