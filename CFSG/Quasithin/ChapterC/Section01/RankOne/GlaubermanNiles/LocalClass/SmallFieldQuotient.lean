module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Kernel
public import Theory.GroupTheory.MinimalParabolicCentral
public import Theory.GroupTheory.GeneralizedFitting.CyclicThree
public import Theory.GroupTheory.SylowKernelInvertedOddLift
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The full local quotient over the two-element field

The marked generalized Fitting subgroup has order three. Its self-centralizer
bounds the whole action quotient by six. A quotient of order three would
kill the original Sylow subgroup, contradicting minimal-parabolic normal
generation. Thus the literal quotient is S₃, identified with PSL₂ over the
given two-element field. No Baumann-fixedness is required in this case.

Source: Aschbacher–Smith C.1.17, printed p.126, at n = 1.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative


namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Group H] [Finite H] {e : B →* H}
  {F : Type} [Field F] [CharP F 2] [Finite F]

theorem InLocalClass.localStar_card_six_of_field_card_two (h : InLocalClass e) (m : NaturalModel e F)
    (hF : Nat.card F = 2) : Nat.card (LocalStar e) = 6 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL := m.actor_card_of_field_card_two e hF
  obtain ⟨hd,hcore⟩ := card_dvd_six_and_twoCore_eq_bot_of_generalizedFitting_card_three hL
  have h3 : 3 ∣ Nat.card (LocalStar e) := hL ▸ (generalizedFitting (LocalStar e)).card_subgroup_dvd_card
  have hne : Nat.card (LocalStar e) ≠ 3 := by
    intro hcard
    obtain ⟨T,_,hT⟩ := h.sylow
    let q := QuotientGroup.mk' (localKernel e)
    have hq := QuotientGroup.mk'_surjective (localKernel e)
    let P := T.mapSurjective hq
    have hP : (P : Subgroup (LocalStar e)) = ⊥ := by
      apply Subgroup.card_eq_one.mp
      rw [P.card_eq_multiplicity,hcard]
      norm_num [Nat.factorization]
    have hTK : (T : Subgroup H) ≤ localKernel e := by
      have hm : (T : Subgroup H).map q = ⊥ := hP
      have hk := (Subgroup.map_eq_bot_iff (T : Subgroup H)).mp hm
      have hqker : q.ker = localKernel e := QuotientGroup.ker_mk' _
      exact hk.trans hqker.le
    have ht := T.normal_eq_top_of_uniqueMaximal hT.1
      ((ChapterB.isMinimalParabolicOver_top_iff T).mp hT).2 (localKernel e) hTK
    exact (h.kernel_sup_sylow_lt_top T).ne (by rw [ht,top_sup_eq])
  have hlo := Nat.le_of_dvd Nat.card_pos h3
  have hhi := Nat.le_of_dvd (by decide : 0 < 6) hd
  interval_cases hc : Nat.card (LocalStar e) <;> norm_num [hc] at *

theorem InLocalClass.localStar_equiv_psl_of_field_card_two (h : InLocalClass e) (m : NaturalModel e F)
    (hF : Nat.card F = 2) : Nonempty (LocalStar e ≃* PSL(2,F)) := by
  have hL := m.actor_card_of_field_card_two e hF
  obtain ⟨eS⟩ := nonempty_mulEquiv_perm_three_of_card_six_core_eq_bot
    (InLocalClass.localStar_card_six_of_field_card_two h m hF) (card_dvd_six_and_twoCore_eq_bot_of_generalizedFitting_card_three hL).2
  obtain ⟨eF⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two hF
  exact ⟨eS.trans eF.symm⟩
end CFSG.Quasithin.ChapterC.GlaubermanNiles
