module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FullOrder
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FullGeneration
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.CubicSmallness

/-!
# Exact ambient order and exclusion of the cubic endpoint branch

The full centralizer comparison gives the native order times the common
endpoint index, which is at most three. The actual marked base generates G.
Its six-path count and odd-shell census force precisely the native order.
Cancelling the nonzero native order therefore makes both endpoint indices
one: Mc = H and M = P₂. This removes the cubic branch in this simple ambient
setting, without assuming the required ambient group isomorphism.

Source: Aschbacher--Smith F.4.12--13,43 and 14.2.18--19, pp.280,296,987.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

private theorem endpoint_index_le_three (r : MarkedTriality T M Mc H) : H.relIndex Mc ≤ 3 := by
  by_cases hp : Mc = H
  · rw [hp,relIndex_self]
    decide
  · have hi := source_short_centralizer_index_three hG hempty hM hu hmany hcard e hH r hp
      1 one_ne_zero
    dsimp only at hi
    rw [source_short_centralizer_index hG hempty hM hu hmany hcard e hH r 1 one_ne_zero,
      source_endpoint_indices hG hempty hM hu hmany hcard e hH r] at hi
    exact hi.le

/-- The original ambient group has the native triality order in both endpoint cases. -/
theorem source_card_eq_triality (r : MarkedTriality T M Mc H) :
    Nat.card G = Nat.card (Carrier P) := by
  let B := H ⊔ secondParabolic T M Mc H
  have hB := source_generated_eq_top hG hempty hM hu hmany hcard e hH r
  have hBG : Nat.card B = Nat.card G := by
    rw [show B = ⊤ from hB]
    exact Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv
  have hc := source_card_eq_triality_mul_index hG hempty hM hu hmany hcard e hH r
  have hb : Nat.card B ≤ Nat.card (Carrier P) * 3 := by
    rw [hBG,hc]
    exact Nat.mul_le_mul_left _ (endpoint_index_le_three hG hempty hM hu hmany hcard e hH r)
  exact hBG.symm.trans
    (ChapterF.SourceCompletion.TrialityTwo.Completion.card_eq_model_of_cubic_order_bound
      (markedCompletion r) hb)

/-- Simplicity and the actual completion geometry eliminate the cubic endpoints. -/
theorem source_endpoints_eq (r : MarkedTriality T M Mc H) :
    Mc = H ∧ secondParabolic T M Mc H = M := by
  have hc := source_card_eq_triality_mul_index hG hempty hM hu hmany hcard e hH r
  rw [source_card_eq_triality hG hempty hM hu hmany hcard e hH r] at hc
  have hi : H.relIndex Mc = 1 := Nat.eq_of_mul_eq_mul_left
    (Nat.card_pos (α := Carrier P)) (by simpa only [mul_one] using hc.symm)
  have hp : Mc = H := le_antisymm (relIndex_eq_one.mp hi)
    (source_first_le_partner hG hempty hM hu hmany hcard e hH)
  exact ⟨hp,source_second_eq_of_partner_eq hG hempty hM hu hmany hcard e hH r hp⟩

/-- The same original marked completion is a generalized hexagon, with the
order bound discharged in both original endpoint cases. -/
theorem source_hexagon (r : MarkedTriality T M Mc H) :
    let c := markedCompletion r
    let Γ := ChapterF.SourceCompletion.TrialityTwo.Completion.graph c
    (∀ v (p : Γ.Walk v v), p.IsCycle → 12 ≤ p.length) ∧
      (∀ v w, Γ.dist v w ≤ 6) ∧
      (∃ v, ∃ p : Γ.Walk v v, p.IsCycle ∧ p.length = 12) := by
  let B := H ⊔ secondParabolic T M Mc H
  apply ChapterF.SourceCompletion.TrialityTwo.Completion.hexagon_metric_of_order_bound
    (markedCompletion r)
  exact (Nat.card_le_card_of_injective B.subtype B.subtype_injective).trans_eq
    (source_card_eq_triality hG hempty hM hu hmany hcard e hH r)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
