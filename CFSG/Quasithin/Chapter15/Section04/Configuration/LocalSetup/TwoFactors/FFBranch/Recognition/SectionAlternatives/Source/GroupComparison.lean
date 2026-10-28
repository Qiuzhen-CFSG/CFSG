module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions.Orders


/-!
# Group obstructions for the surviving FF sections

The eight actual small-actor models have orders dividing 60480. Thus their
Sylow two-subgroups have order at most 64. An embedded binary SL₂ component
has bounded field degree; if the quotient by it is a two-group, its odd
part must also agree with the actor's. The explicit order formulas exclude
every such rank-one component. Binary SL₄ and SL₅ cannot even embed, by
their orders and defining two-parts.

The source-section extraction uses these obstructions on the literal
F*(N) inside the offender actor N. The two-group quotient is supplied by
B.5.1(1)'s Sylow supplement, not by an equality between N and the ambient
representation quotient. All comparisons use actual group equivalences.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.2, p.86; B.5.1, p.99; the comparison in 15.4.18, p.1163.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open ClassificationComparison ClassificationComparison.FFAlternatives ClassificationComparison.QuasisimpleComparison
namespace SourceSections
universe u
variable {A : Type u} [Group A] [Finite A]

/-- A uniform Sylow bound from the actual small-actor orders. -/
theorem small_sylow (ha : SmallActorModel A) (S : Sylow 2 A) : Nat.card S ≤ 128 := by
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hd : 2 ^ k ∣ 60480 := by
    rw [← hk]
    exact (S : Subgroup A).card_subgroup_dvd_card.trans (AmbientExtensions.actor_card_dvd ha)
  have hb : k ≤ 6 := by
    by_contra hn
    have h128 : 128 ∣ 60480 := (pow_dvd_pow 2 (by omega : 7 ≤ k)).trans hd
    norm_num at h128
  rw [hk]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hb).trans (by decide)

private theorem odd_dvd_component (L : Subgroup A) [L.Normal]
    (hq : IsPGroup 2 (A ⧸ L)) {m : ℕ} (hm : Odd m) :
    m ∣ Nat.card A → m ∣ Nat.card L := by
  obtain ⟨k, hk⟩ := hq.exists_card_eq
  have he : Nat.card A = Nat.card L * 2 ^ k := by
    rw [← hk, ← Subgroup.index_eq_card, Subgroup.card_mul_index]
  intro hd
  rw [he] at hd
  exact ((Nat.coprime_two_right.mpr hm).pow_right k).dvd_of_dvd_mul_right hd

/-- A normal binary rank-one subgroup cannot have two-group quotient in any
of the surviving actors. The odd-divisor comparison is essential here. -/
theorem no_linearTwo (ha : SmallActorModel A) (L : Subgroup A) [L.Normal]
    (hq : IsPGroup 2 (A ⧸ L)) (F : BinaryField) (e : L ≃* SL(2,F.Carrier)) : False := by
  have hb := linearTwo_degree_le (small_sylow ha) F
    (L.subtype.comp e.symm.toMonoidHom) (Subtype.val_injective.comp e.symm.injective)
  have hc : Nat.card L = 2 ^ F.degree * ((2 ^ F.degree) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula, F.card_eq]
  have hd := L.card_subgroup_dvd_card
  have h9 := odd_dvd_component L hq (by decide : Odd 9)
  have h5 := odd_dvd_component L hq (by decide : Odd 5)
  have h27 := odd_dvd_component L hq (by decide : Odd 27)
  have h7 := odd_dvd_component L hq (by decide : Odd 7)
  rw [hc] at hd h9 h5 h27 h7
  have hp := F.degree_pos
  interval_cases hn : F.degree <;>
    rcases AmbientExtensions.actor_card ha with ha | ha | ha | ha | ha | ha | ha | ha
  all_goals
    solve
    | norm_num [ha, hn] at hd
    | norm_num [ha, hn] at h9
    | norm_num [ha, hn] at h5
    | norm_num [ha, hn] at h27
    | norm_num [ha, hn] at h7

/-- Neither binary rank-four nor rank-five linear groups embed in a small actor. -/
theorem no_linearFourFive (ha : SmallActorModel A) (L : Subgroup A)
    (d : ℕ) (hd : d = 4 ∨ d = 5) (e : L ≃* SL(d,ZMod 2)) : False := by
  rcases hd with rfl | rfl
  · have hc : Nat.card A ≤ 12096 := by have := AmbientExtensions.actor_card ha; omega
    have hs : Nat.card SL(4,ZMod 2) ∣ Nat.card A := by
      rw [← Nat.card_congr e.toEquiv]
      exact L.card_subgroup_dvd_card
    have hd := (card_dvd_of_surjective (QuotientGroup.mk' (center SL(4,ZMod 2)))
      (QuotientGroup.mk'_surjective _)).trans hs
    have hp := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 4
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Fin.val_zero, Fin.val_succ, Nat.mul_one] at hp
    rw [hp] at hd
    have := Nat.le_of_dvd (Nat.card_pos (α := A)) hd
    omega
  · exact no_linearFive (small_sylow ha)
      (L.subtype.comp e.symm.toMonoidHom) (Subtype.val_injective.comp e.symm.injective)

end SourceSections
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
