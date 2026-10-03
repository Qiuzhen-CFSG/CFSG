module
public import ABG.ChapterII.Section1.WreathedPresentation
/-!
# Coordinates and commutativity of the wreathed base

The subgroup `U = ⟨s,t⟩` appearing in ABG Chapter II §1 Lemma 2 (article
pp.9–10) consists exactly of integer-power products `s^i * t^j`. Closure
induction uses the defining commutation relation to collect both powers;
commutativity of arbitrary base elements then follows from that of the two
generators. These facts support the later analysis of elements outside `U`.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

public theorem mem_U_iff (g : S) : g ∈ P.U ↔ ∃ i j : ℤ, P.s ^ i * P.t ^ j = g := by
  have hc : Commute P.s P.t := P.commute
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem a ha =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul a b ha hb ia ib =>
      rcases ia with ⟨i, j, rfl⟩
      rcases ib with ⟨k, l, rfl⟩
      refine ⟨i + k, j + l, ?_⟩
      rw [zpow_add, zpow_add]
      calc
        _ = P.s ^ i * (P.s ^ k * P.t ^ j) * P.t ^ l := by group
        _ = _ := by rw [(hc.zpow_zpow k j).eq]; group
    | inv a ha ih =>
      rcases ih with ⟨i, j, rfl⟩
      exact ⟨-i, -j, by simp [zpow_neg, mul_inv_rev, (hc.zpow_zpow i j).inv_inv.eq]⟩
  · rintro ⟨i, j, rfl⟩
    exact P.U.mul_mem (P.U.zpow_mem (Subgroup.subset_closure (by simp)) i)
      (P.U.zpow_mem (Subgroup.subset_closure (by simp)) j)

public theorem commute_of_mem_U {a b : S} (ha : a ∈ P.U) (hb : b ∈ P.U) :
    Commute a b := by
  rcases (P.mem_U_iff a).mp ha with ⟨i, j, rfl⟩
  rcases (P.mem_U_iff b).mp hb with ⟨k, l, rfl⟩
  have hc : Commute P.s P.t := P.commute
  exact ((Commute.self_zpow _ _).zpow_left i).mul_right (hc.zpow_zpow i l) |>.mul_left
    ((hc.symm.zpow_zpow j k).mul_right ((Commute.self_zpow _ _).zpow_left j))

end ABG.Wreathed.Presentation
