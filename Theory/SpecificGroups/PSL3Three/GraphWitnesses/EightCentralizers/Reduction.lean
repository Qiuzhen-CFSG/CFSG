module

public import Theory.SpecificGroups.PSL3Three.Basic
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.OddThreeRank
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Reducing an elementary eight-subgroup to inverse transpose

The known two-rank bound of PSL₃(3) forces an elementary eight-subgroup of
its automorphism group to contain an outer element. Its involutory order
then permits use of outer-involution conjugacy. Conjugating the entire
subgroup preserves innerness, fixed elements, and the literal displacement
`a c * c⁻¹`; the selected final outer involution need not be the first one.

The graph-case calculation is explicit in the reduction theorem. It is
discharged by the conditional structural assembly in the parent module;
this reduction alone is not the native elementary-eight calculation.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2,
manuscript p.10.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Matrix.PSL3Three.GraphWitnesses.EightCentralizers

theorem psl_center_eq_bot : center PSL = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨s, rfl⟩ := project_surjective x
  have hs : s ∈ center SL := by
    rw [mem_center_iff]
    intro y
    apply project_injective
    simpa only [map_mul] using (mem_center_iff.mp hx (project y))
  have hs1 : s = 1 := by simpa only [center_eq_bot, mem_bot] using hs
  simp [hs1]

theorem elementary_eight_has_outer (B : Subgroup (MulAut PSL))
    (hB : IsElementaryAbelian 2 B) (hc : Nat.card B = 8) :
    ∃ b ∈ B, b ∉ MulAut.innerSubgroup PSL := by
  by_contra! hn
  let : IsElementaryAbelian 2 B := hB
  let e : PSL ≃* MulAut.innerSubgroup PSL :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot)
  let D := B.subgroupOf (MulAut.innerSubgroup PSL)
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf hn
  have hb := (primeRank_le_iff_elementary_card_le PSL).mp
    (Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le
      Nat.prime_three (by decide) (by simp))
    (D.map e.symm.toMonoidHom) (IsElementaryAbelian.map _)
  rw [Subgroup.card_map_of_injective e.symm.injective,
    Nat.card_congr (subgroupOfEquivOfLe hn).toEquiv, hc] at hb
  norm_num at hb

theorem inner_conjugate_iff (u a : MulAut PSL) :
    u * a * u⁻¹ ∈ MulAut.innerSubgroup PSL ↔ a ∈ MulAut.innerSubgroup PSL := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨u.symm x, ?_⟩
    have he : MulAut.conj (u.symm x) = u⁻¹ * MulAut.conj x * u := by ext y; simp
    rw [he, hx]
    group
  · rintro ⟨x, rfl⟩
    exact ⟨u x, by ext y; simp⟩

theorem eight_witness_of_graph_case
    (hconj : ∀ b : MulAut PSL, orderOf b = 2 →
      b ∉ MulAut.innerSubgroup PSL → ∃ u : MulAut PSL,
        b = u * Matrix.PSL3.OuterSolvable.graph (ZMod 3) * u⁻¹)
    (hgraph : ∀ D : Subgroup (MulAut PSL), IsElementaryAbelian 2 D →
      Nat.card D = 8 → Matrix.PSL3.OuterSolvable.graph (ZMod 3) ∈ D →
      ∃ b ∈ D, b ∉ MulAut.innerSubgroup PSL ∧ ∃ a ∈ D, ∃ c : PSL,
        b c = c ∧ orderOf (a c * c⁻¹) = 3)
    (B : Subgroup (MulAut PSL)) (hB : IsElementaryAbelian 2 B)
    (hc : Nat.card B = 8) :
    ∃ b ∈ B, b ∉ MulAut.innerSubgroup PSL ∧ ∃ a ∈ B, ∃ c : PSL,
      b c = c ∧ orderOf (a c * c⁻¹) = 3 := by
  let : IsElementaryAbelian 2 B := hB
  obtain ⟨b, hb, hout⟩ := elementary_eight_has_outer B hB hc
  have hb2 : orderOf b = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian b hb)
    (fun h => hout (h ▸ (MulAut.innerSubgroup PSL).one_mem))
  obtain ⟨u, rfl⟩ := hconj b hb2 hout
  let D := B.map (MulAut.conj u⁻¹).toMonoidHom
  have hD : IsElementaryAbelian 2 D := IsElementaryAbelian.map _
  have hDc : Nat.card D = 8 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective, hc]
  have hDg : Matrix.PSL3.OuterSolvable.graph (ZMod 3) ∈ D := by
    refine ⟨_, hb, ?_⟩
    change u⁻¹ * (u * Matrix.PSL3.OuterSolvable.graph (ZMod 3) * u⁻¹) * (u⁻¹)⁻¹ = _
    group
  obtain ⟨d, hd, hdout, a, ha, c, hdc, hac⟩ := hgraph D hD hDc hDg
  have hback {x : MulAut PSL} (hx : x ∈ D) : u * x * u⁻¹ ∈ B := by
    obtain ⟨y, hy, rfl⟩ := hx
    have he : u * (MulAut.conj u⁻¹) y * u⁻¹ = y := by
      change u * (u⁻¹ * y * (u⁻¹)⁻¹) * u⁻¹ = y
      group
    change u * (MulAut.conj u⁻¹) y * u⁻¹ ∈ B
    rw [he]
    exact hy
  refine ⟨u * d * u⁻¹, hback hd,
    fun hi => hdout ((inner_conjugate_iff u d).mp hi),
    u * a * u⁻¹, hback ha, u c, ?_, ?_⟩
  · change u (d (u.symm (u c))) = u c
    rw [u.symm_apply_apply, hdc]
  · change orderOf (u (a (u.symm (u c))) * (u c)⁻¹) = 3
    rw [u.symm_apply_apply, ← map_inv, ← map_mul, u.orderOf_eq, hac]

end Matrix.PSL3Three.GraphWitnesses.EightCentralizers
