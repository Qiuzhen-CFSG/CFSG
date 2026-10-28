module

public import ABG.ChapterII.Section1.WreathedOuterCentralizers

/-!
# Elements of order eight in the wreathed group of order 32

Such an element lies outside the abelian base, which has exponent four.
Its square generates the center, of order four. The outer-centralizer
formula therefore shows that the element generates its own centralizer.

Source: ABG II.1 Lemma 2; Fong, J. Algebra 6 (1967), p.70.
-/

namespace ABG.Wreathed.Presentation

public theorem centralizer_eq_zpowers_of_order_eight
    {S : Type*} [Group S] [Finite S] (P : Presentation S 2)
    (g : S) (hg : orderOf g = 8) :
    Subgroup.centralizer ({g} : Set S) = Subgroup.zpowers g := by
  have hgU : g ∉ P.U := by
    intro h
    obtain ⟨i, j, rfl⟩ := (P.mem_U_iff _).mp h
    have hpow : (P.s ^ i * P.t ^ j) ^ 4 = 1 := by
      rw [(show Commute P.s P.t from P.commute).zpow_zpow i j |>.mul_pow]
      have hs : (P.s ^ i) ^ (4 : ℕ) = (P.s ^ (4 : ℕ)) ^ i := by simpa using zpow_comm P.s i 4
      have ht : (P.t ^ j) ^ (4 : ℕ) = (P.t ^ (4 : ℕ)) ^ j := by simpa using zpow_comm P.t j 4
      rw [hs, ht]
      simp only [show P.s ^ 4 = 1 from P.s_pow, show P.t ^ 4 = 1 from P.t_pow,
        one_zpow, one_mul]
    have hd := orderOf_dvd_of_pow_eq_one hpow
    rw [hg] at hd
    norm_num at hd
  have hsquare : Subgroup.zpowers (g ^ 2) = Subgroup.center S := by
    apply Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (Subgroup.mem_center_iff.mpr
        (fun a => (P.outer_square_commute hgU a).symm.eq)))
    rw [P.card_center, Nat.card_zpowers, orderOf_pow, hg]
    norm_num
  rw [P.outer_centralizer_eq hgU, sup_eq_right.mpr]
  rw [← hsquare]
  exact Subgroup.zpowers_le.mpr ((Subgroup.zpowers g).pow_mem (Subgroup.mem_zpowers g) 2)

end ABG.Wreathed.Presentation
