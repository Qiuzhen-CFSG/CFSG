module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# Comparing the six component-action alternatives

The binary quotient has order 20160 or 9999360. These orders exclude
G₂(4) and both alternating actions, including their perfect triple covers.
In the odd linear case the actual PSL group is centerless; its small
nonsimple parameters cannot have the specified binary quotient.

The six-case theorem takes the PSL₃(4) and sporadic model separations
proved in the sibling modules as explicit inputs. It does not assume a simple component,
a split central cover, or an inner action. Those conclusions are derived
from the literal alternatives of 1.1.5(3).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
1.1.5(3), printed pp.501–503; proof of 15.4.20, printed p.1164.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.BinaryModels
open ClassificationModels Chapter15.Section03.Candidates.ComponentStructure
universe u

/-- Orders derived from the actual projective matrix models. -/
theorem binary_card {L : Type*} [Group L] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL L n 2) :
    Nat.card L = if n = 4 then 20160 else 9999360 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let _ : NeZero n := ⟨by omega⟩
  have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) n
  rw [← Nat.card_congr e.toEquiv, hF] at hh
  rcases hn with rfl | rfl
  · norm_num [Fin.prod_univ_succ] at hh ⊢
    exact hh
  · norm_num [Fin.prod_univ_succ] at hh ⊢
    exact hh

private theorem simple_perfect_center {L : Type*} [Group L]
    [IsSimpleGroup L] [Group.IsPerfect L] : center L = ⊥ := by
  rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp h)).elim

/-- The G₂(4) order differs from both binary orders. -/
theorem not_g2_four {L : Type*} [Group L] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hbin : ClassicalGroup.IsPSL L n 2) (hg2 : IsG2At L 4) : False := by
  have hb := binary_card hn hbin
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hg2
  have he := Nat.card_congr e.toEquiv
  rw [Atlas.G2.card_Model, hF] at he
  rcases hn with rfl | rfl <;> norm_num at hb he <;> omega

/-- The alternating actions, including the perfect central triple covers,
are incompatible with the actual binary quotient. -/
theorem not_alternating_action {L : Type*} [Group L] {n m : ℕ}
    (hn : n = 4 ∨ n = 5) (hm : m = 6 ∨ m = 7)
    (hcenter : center L = pCore 2 L)
    (hbin : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) n 2)
    (α : MulAut L) (σ : Equiv.Perm (Fin m)) (ha : AlternatingAction α m σ) : False := by
  have hb := binary_card hn hbin
  rcases ha with ⟨e, _⟩ | ⟨_, _, e, _⟩
  · have hd : Nat.card (L ⧸ pCore 2 L) ∣ Nat.card L :=
      Subgroup.card_dvd_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have he := Nat.card_congr e.toEquiv
    rcases hm with rfl | rfl <;>
      rw [nat_card_alternatingGroup] at he <;> norm_num [Nat.factorial] at he <;>
      rw [he, hb] at hd <;> rcases hn with rfl | rfl <;> norm_num at hd
  · have he := Nat.card_congr e.toEquiv
    rw [hcenter] at he
    rcases hm with rfl | rfl <;>
      rw [nat_card_alternatingGroup] at he <;> norm_num [Nat.factorial] at he <;>
      rcases hn with rfl | rfl <;> norm_num at hb <;> omega

private theorem small_rank_one_card {L : Type*} [Group L] {p : ℕ}
    (hp : p = 2 ∨ p = 3) (hm : ClassicalGroup.IsPSL L 2 p) :
    Nat.card L = if p = 2 then 6 else 12 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
  rw [← Nat.card_congr e.toEquiv, hF] at hh
  rcases hp with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at hh ⊢ <;> omega

/-- In the odd linear alternative the group itself is centerless. Small
PSL₂ fields are excluded using the size of its already identified quotient. -/
theorem odd_model_center_eq_bot {L : Type*} [Group L] [Group.IsPerfect L]
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hbin : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) n 2)
    (hm : ClassicalGroup.IsPSL L 3 3 ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) : center L = ⊥ := by
  rcases hm with hm | ⟨p, hp, hm⟩
  · obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
    let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup L := e.isSimpleGroup
    exact simple_perfect_center
  · have hp4 : 4 ≤ p := by
      by_contra h
      have hp23 : p = 2 ∨ p = 3 := by have := hp.1.two_le; omega
      have hc := small_rank_one_card hp23 hm
      have hd : Nat.card (L ⧸ pCore 2 L) ∣ Nat.card L :=
        Subgroup.card_dvd_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      rw [hc, binary_card hn hbin] at hd
      rcases hn with rfl | rfl <;> rcases hp23 with rfl | rfl <;> norm_num at hd
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    let : IsSimpleGroup L := e.isSimpleGroup
    exact simple_perfect_center

/-- Full six-alternative comparison, conditional only on the two independent
model-separation statements. -/
theorem model_action_of_separation
    (h34 : ∀ {Q : Type u} [Group Q] {n : ℕ}, (n = 4 ∨ n = 5) →
      ClassicalGroup.IsPSL Q 3 4 → ¬ ClassicalGroup.IsPSL Q n 2)
    (hspor : ∀ (name : SporadicName) {n : ℕ}, (n = 4 ∨ n = 5) → name ≠ .j3 →
      ¬ ClassicalGroup.IsPSL name.Carrier n 2)
    {L : Type u} [Group L] [IsQuasisimple L] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hcenter : center L = pCore 2 L)
    (hbin : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) n 2)
    {α : MulAut L} (ha : ModelAction115 L α) :
    center L = ⊥ ∧ α ∈ (MulAut.conj (G := L)).range := by
  cases ha with
  | lie hs _ hi =>
    let := hs
    exact ⟨simple_perfect_center, hi⟩
  | two_cover _ _ hm _ =>
    rcases hm with hm | hm
    · exact (h34 hn hm hbin).elim
    · exact (not_g2_four hn hbin hm).elim
  | six σ _ ha => exact (not_alternating_action hn (Or.inl rfl) hcenter hbin α σ ha).elim
  | seven σ _ ha => exact (not_alternating_action hn (Or.inr rfl) hcenter hbin α σ ha).elim
  | odd hm hi => exact ⟨odd_model_center_eq_bot hn hbin hm, hi⟩
  | sporadic name hne hm _ =>
    obtain ⟨e⟩ := hm
    exact (hspor name hn hne (hbin.of_mulEquiv e.symm)).elim

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.BinaryModels
