module

public import ABG.ChapterII.Section1.FourSubgroups
public import ABG.ChapterII.Section1.Center
public import ABG.ChapterII.Section1.WreathedFourSubgroups
public import ABG.ChapterII.Section1.WreathedCenter

/-!
# Klein four subgroups meet the center

Every Klein four subgroup of a semidihedral or wreathed group meets the
center nontrivially. In the semidihedral case the four-subgroup conjugacy
representative is self-centralizing, so it contains the center of order two.
In the wreathed case both four-subgroup representatives contain the same
central involution, which conjugation fixes.

This is the local obstruction to splitting the central PSL2 preimage in
ABG Chapter II, Section3, Proposition2 (article p22), deduced from the
proved Section1 four-subgroup classifications. It imposes no rank bound
as a separate hypothesis.
-/

public section
namespace ABG

private theorem central_mem_conjugate
    {S : Type*} [Group S] {x : S} (hx : x ∈ Subgroup.center S)
    (V : Subgroup S) (hxV : x ∈ V) (g : S) :
    x ∈ V.map (MulAut.conj g).toMonoidHom := by
  refine ⟨x, hxV, ?_⟩
  change g * x * g⁻¹ = x
  rw [Subgroup.mem_center_iff.mp hx g]
  simp

theorem four_subgroup_inf_center_ne_bot
    {S : Type*} [Group S]
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (V : Subgroup S) (hV : IsKleinFour V) :
    V ⊓ Subgroup.center S ≠ ⊥ := by
  rcases hS with hS | ⟨n, hn⟩
  · obtain ⟨U, _hU, hconj, hCU, _hNU⟩ := QuasiDihedral.four_subgroups hS
    obtain ⟨g, hg⟩ := hconj V hV
    have hcenter : Subgroup.center S ≤ V := by
      intro x hx
      rw [← hg]
      apply central_mem_conjugate hx U
      apply hCU
      exact Subgroup.center_le_centralizer _ hx
    have hcard := QuasiDihedral.card_center hS
    intro hbot
    have heq : Subgroup.center S = ⊥ := by
      simpa [inf_eq_right.mpr hcenter] using hbot
    rw [heq, Subgroup.card_bot] at hcard
    contradiction
  · obtain ⟨P⟩ := Wreathed.nonempty_presentation hn
    have hxcenter := P.x_mem_center
    have hxV : P.x ∈ V := by
      by_cases hVT : V = P.T
      · rw [hVT]
        exact Subgroup.subset_closure (by simp)
      · obtain ⟨g, hg⟩ := P.four_subgroup_classes.2.2 V hV hVT
        rw [← hg]
        exact central_mem_conjugate hxcenter P.T₀
          (Subgroup.subset_closure (by simp)) g
    intro hbot
    have hxone : P.x = 1 := Subgroup.mem_bot.mp (hbot ▸ ⟨hxV, hxcenter⟩)
    have horder := P.x_orderOf
    simp [hxone] at horder

end ABG
