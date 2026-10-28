module
public import Theory.SpecificGroups.SymmetricFive.EvenInvolutionCentralizer
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# Cubic normalizers of subgroups of order four in S₅

A subgroup of order four normalized by an element of order three lies in
A₅. Otherwise its intersection with A₅ has order two and is centralized
by that element. An even involution has centralizer of order eight,
which excludes an element of order three.
Source application: Aschbacher–Smith 14.2.16 and 14.3.15, pp.986,994.
-/
public noncomputable section
open Subgroup

namespace Theory.SpecificGroups.SymmetricFive

theorem four_le_alternating_of_normalized_by_three
    (R : Subgroup (Equiv.Perm (Fin 5))) (hR : Nat.card R = 4)
    (b : Equiv.Perm (Fin 5)) (hb : orderOf b = 3)
    (hn : b ∈ normalizer (R : Set _)) : R ≤ alternatingGroup (Fin 5) := by
  let A := alternatingGroup (Fin 5)
  have hd : A.relIndex R ∣ 2 := by
    simpa only [A,alternatingGroup.index_eq_two] using A.relIndex_dvd_index_of_normal R
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact relIndex_eq_one.mp h1
  · let N := R ⊓ A
    have hc : Nat.card N = 2 := by
      have hh := relIndex_mul_card_of_le (show R ⊓ A ≤ R from inf_le_left)
      rw [inf_comm R A,inf_relIndex_right,h2,hR] at hh
      change Nat.card N = 2
      dsimp only [N]
      rw [inf_comm]
      omega
    have hbN : b ∈ normalizer (N : Set _) := inf_normalizer_le_normalizer_inf
      ⟨hn,le_normalizer_of_normal (mem_top _)⟩
    obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 (by rw [hc])
    have hab : Commute (a : Equiv.Perm (Fin 5)) b :=
      (normalizer_le_centralizer_of_card_two N hc hbN) a a.property
    exact (Equiv.Perm.three_not_commute_even_involution_five a b
      ((orderOf_coe a).trans ha) a.property.2 hb hab).elim
end Theory.SpecificGroups.SymmetricFive
