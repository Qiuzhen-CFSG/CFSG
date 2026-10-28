module
public import Theory.GroupTheory.SpecificGroups.DihedralFiveAutomorphisms
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# The two-part of the order-ten dihedral automorphism group

Centerlessness embeds the ten inner automorphisms, while the marked
rotation/reflection calculation bounds the full automorphism group by
twenty. Its Sylow two-subgroups therefore have order at most four.
This is the precise model bound consumed by DihedralLocal to establish
the truncated Suzuki source's panel regularity.
Source: DGS, Groups and Graphs, (6.1) and its remark, pp.118--119.
-/

public noncomputable section
open Subgroup
namespace DihedralGroup
/-- Every two-subgroup of the actual D₁₀ automorphism group has order at most four. -/
theorem five_aut_two_subgroup_bound (V : Subgroup (MulAut (DihedralGroup 5)))
    (hV : IsPGroup 2 V) : Nat.card V ≤ 4 := by
  have hc : Nat.card (MulAut (DihedralGroup 5)) = 10 ∨
      Nat.card (MulAut (DihedralGroup 5)) = 20 := by
    have hd : 10 ∣ Nat.card (MulAut (DihedralGroup 5)) := by
      have hi := MonoidHom.ofInjective
        (Theory.GroupTheory.conj_injective_of_center_eq_bot five_center_eq_bot)
      have he : Nat.card (MulAut.conj : DihedralGroup 5 →* MulAut (DihedralGroup 5)).range = 10 := by
        rw [← Nat.card_congr hi.toEquiv, DihedralGroup.nat_card]
      exact he ▸ (MulAut.conj : DihedralGroup 5 →* MulAut (DihedralGroup 5)).range.card_subgroup_dvd_card
    have hp := Nat.card_pos (α := MulAut (DihedralGroup 5))
    have hb := card_mulAut_five_le_twenty
    omega
  obtain ⟨T,hT⟩ := hV.exists_le_sylow
  have hb := Nat.card_le_card_of_injective (inclusion hT) (inclusion_injective hT)
  rcases hc with hc | hc
  · have he : Nat.card T = 2 := by rw [T.card_eq_multiplicity,hc]; decide +kernel
    omega
  · have he : Nat.card T = 4 := by rw [T.card_eq_multiplicity,hc]; decide +kernel
    omega
end DihedralGroup

