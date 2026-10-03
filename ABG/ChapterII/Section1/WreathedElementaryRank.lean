module

public import ABG.ChapterII.Section1.WreathedFourSubgroups
public import Theory.ElementaryAbelian.Basic

/-!
# Elementary subgroups of wreathed two-groups

Every elementary abelian subgroup of a wreathed two-group has order at most
four. Inside the base, its elements belong to the base four. Otherwise an
outer involution can be conjugated to the swapping generator, whose commuting
involutions lie in the outer four. This uses the coordinates of ABG II.1,
Lemma 2, and applies at every height at least two.
-/

namespace ABG.Wreathed.Presentation

variable {S : Type*} [Group S] [Finite S] {n : ℕ}

/-- Wreathed two-groups have elementary rank at most two. -/
public theorem elementary_card_le_four (P : Presentation S n)
    (A : Subgroup S) [IsElementaryAbelian 2 A] : Nat.card A ≤ 4 := by
  classical
  have hsq (a : S) (ha : a ∈ A) : a ^ 2 = 1 := by
    exact congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) (⟨a, ha⟩ : A))
  by_cases hAU : A ≤ P.U
  · have hAT : A ≤ P.T := by
      intro a ha
      rcases P.base_involution_cases (hAU ha) (hsq a ha) with h | h | h | h
      · rw [h]; exact P.T.one_mem
      all_goals rw [h]; exact Subgroup.subset_closure (by simp)
    exact (Subgroup.card_le_of_le hAT).trans_eq P.T_isFourGroup.card_four
  · obtain ⟨a, ha, haU⟩ := Set.not_subset.mp hAU
    obtain ⟨g, hg⟩ := isConj_iff.mp (P.outer_involution_isConj haU (hsq a ha))
    let e := MulAut.conj g
    have he : e a = P.z := hg
    have hmap : A.map e.toMonoidHom ≤ P.T₀ := by
      rintro y ⟨b, hb, rfl⟩
      apply P.commuting_involution_mem_T₀
      · change (e b) ^ 2 = 1
        rw [← map_pow, hsq b hb, map_one]
      · rw [← he]
        change e b * e a = e a * e b
        rw [← map_mul, ← map_mul]
        exact congrArg e (congrArg Subtype.val
          (IsMulCommutative.is_comm.comm (⟨b, hb⟩ : A) (⟨a, ha⟩ : A)))
    have hc := Subgroup.card_le_of_le hmap
    rwa [Subgroup.card_map_of_injective e.injective, P.T₀_isFourGroup.card_four] at hc

end ABG.Wreathed.Presentation

namespace ABG

/-- The presentation-independent elementary-rank bound for wreathed groups. -/
public theorem elementary_card_le_four_of_isWreathedOfHeight
    {S : Type*} [Group S] [Finite S] {n : ℕ} (hS : IsWreathedOfHeight S n)
    (A : Subgroup S) [IsElementaryAbelian 2 A] : Nat.card A ≤ 4 := by
  obtain ⟨P⟩ := Wreathed.nonempty_presentation hS
  exact P.elementary_card_le_four A

end ABG
