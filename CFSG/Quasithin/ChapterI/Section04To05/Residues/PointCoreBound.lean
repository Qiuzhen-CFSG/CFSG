module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PointCoreFiveAction

/-!
# The original point two-core has order at least 32

The actual A₆/S₆ point quotient is center-free, so Z(G₀) lies in Q₀.
A five-element of G₀ acts nontrivially on Q₀. If Z(G₀) is nontrivial,
this action has a nonidentity fixed point, and the elementary five-orbit
bound gives |Q₀|≥32. The alternative in D5 gives that bound directly.

This discharges the local core-order input to I.5.15 using the original
D-system and the previously proved kernel separation.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem point_center_le_core : center (S.family 0) ≤ pCore 2 (S.family 0) := by
  have h {K : Type} [Group K]
      (e : (S.family 0 ⧸ pCore 2 (S.family 0)) ≃* K) (hz : center K = ⊥) :
      center (S.family 0) ≤ pCore 2 (S.family 0) := by
    intro a ha
    have hfa : S.localQuotientMap 0 e a ∈ center K := by
      rw [mem_center_iff]
      intro b
      obtain ⟨c, rfl⟩ := S.localQuotientMap_surjective 0 e b
      simpa only [map_mul] using congrArg (S.localQuotientMap 0 e) (mem_center_iff.mp ha c)
    rw [hz, mem_bot] at hfa
    have hk : a ∈ (S.localQuotientMap 0 e).ker := hfa
    rwa [S.localQuotientMap_ker] at hk
  rcases S.point_C3 rfl with he | he
  · obtain ⟨e⟩ := he
    exact h e Theory.SpecificGroups.SymmetricSix.a6_center_eq_bot
  · obtain ⟨e⟩ := he
    exact h e Theory.SpecificGroups.SymmetricSix.s6_center_eq_bot

/-- The local lower bound needed by the actual six-space full-image argument. -/
theorem point_core_card_ge_thirty_two : 32 ≤ Nat.card (pCore 2 (S.family 0)) := by
  rcases S.nondegenerate rfl with hz | hc
  swap
  · exact hc.le
  obtain ⟨a, ha⟩ := S.exists_point_five_element
  let A := zpowers a
  let Q := pCore 2 (S.family 0)
  have hA : Nat.card A = 5 := (Nat.card_zpowers a).trans ha
  have hmove : FixedPoints.subgroup A Q ≠ ⊤ := by
    intro ht
    apply S.point_five_not_centralizes_core a ha
    rw [mem_centralizer_iff]
    rintro q ⟨v, hv, rfl⟩
    have hf : (⟨v, hv⟩ : Q) ∈ FixedPoints.subgroup A Q := ht ▸ mem_top _
    have he := congrArg (fun w : Q => (w.val : G)) (hf ⟨a, mem_zpowers a⟩)
    change a.val * v.val * a.val⁻¹ = v.val at he
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  have hfixed : FixedPoints.subgroup A Q ≠ ⊥ := by
    intro hb
    have hz' : ∃ z : S.family 0, z ∈ center (S.family 0) ∧ z ≠ 1 := by
      simpa only [ne_eq, mem_bot] using SetLike.not_le_iff_exists.mp (show ¬ center (S.family 0) ≤ ⊥ from
        fun h => hz (le_bot_iff.mp h))
    obtain ⟨z, hzmem, hzne⟩ := hz'
    let v : Q := ⟨z, S.point_center_le_core hzmem⟩
    have hv : v ∈ FixedPoints.subgroup A Q := by
      intro b
      apply Subtype.ext
      change b.val * z * b.val⁻¹ = z
      rw [mem_center_iff.mp hzmem b.val, mul_inv_cancel_right]
    rw [hb, mem_bot] at hv
    exact hzne (congrArg Subtype.val hv)
  exact Theory.GroupAction.thirty_two_le_card_of_five_action_fixed
    hA pCore_isPGroup hmove hfixed

end Quasithin.I5.DSystem
