module

public import Theory.GroupTheory.PResidual.PerfectCover
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal

/-!
# Normal Sylow three-subgroups from a small two-residual

If the two-residual of a finite group has order dividing six, its Sylow
three-subgroups have index one or two. The index-two quotient is excluded
by two-perfectness. The residual is therefore a three-group and, since its
ambient quotient is a two-group, it is the unique Sylow three-subgroup.

This is the small-section step in the centralizer argument of Goldschmidt,
*Automorphisms of trivalent graphs* (1980), §5.
-/

public section

open Subgroup

private theorem threeGroup_of_twoPerfect_card_dvd_six
    {G : Type*} [Group G] [Finite G] (hp : IsPPerfect 2 G)
    (hc : Nat.card G ∣ 6) : IsPGroup 3 G := by
  let P : Sylow 3 G := Sylow.nonempty.some
  have hd : P.index ∣ 6 := (P : Subgroup G).index_dvd_card.trans hc
  have hn : ¬ 3 ∣ P.index := P.not_dvd_index
  have hi : P.index = 1 ∨ P.index = 2 := by
    have hb : P.index ≤ 6 := Nat.le_of_dvd (by decide) hd
    interval_cases h : P.index <;> norm_num [h] at *
  have he : (P : Subgroup G) = ⊤ := by
    rcases hi with hi | hi
    · exact Subgroup.index_eq_one.mp hi
    · let hN : (P : Subgroup G).Normal := Subgroup.normal_of_index_eq_two hi
      exact hp P hN (IsPGroup.of_card (n := 1)
        (by simpa only [← Subgroup.index_eq_card, pow_one] using hi))
  exact P.isPGroup'.of_equiv ((MulEquiv.subgroupCongr he).trans Subgroup.topEquiv)

/-- A two-residual of order dividing six forces every Sylow three-subgroup
to be normal. -/
theorem Sylow.normal_of_twoResidual_card_dvd_six
    {G : Type*} [Group G] [Finite G] (P : Sylow 3 G)
    (hc : Nat.card (pResidual 2 G) ∣ 6) : (P : Subgroup G).Normal := by
  have hr : IsPGroup 3 (pResidual 2 G) :=
    threeGroup_of_twoPerfect_card_dvd_six (Subgroup.isPPerfect_pResidual 2) hc
  have hi : ¬ 3 ∣ (pResidual 2 G).index := by
    obtain ⟨n, hn⟩ := (Subgroup.isPGroup_quotient_pResidual (G := G) 2).exists_card_eq
    change ¬ 3 ∣ Nat.card (G ⧸ pResidual 2 G)
    rw [hn]
    intro hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  let Q : Sylow 3 G := hr.toSylow hi
  have hQ : (Q : Subgroup G).Normal := inferInstanceAs (pResidual 2 G).Normal
  let := Q.unique_of_normal hQ
  exact P.normal_of_subsingleton

end
