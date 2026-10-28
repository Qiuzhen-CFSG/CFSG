module
public import Theory.GroupTheory.NoncentralChiefRefinement.Actions

/-!
# Counting surviving normal strata

Chief refinements of consecutive normal intervals concatenate, and their
noncentral binary counts add. In particular each noncentral binary stratum
contributes at least one when its chief refinements contain a noncentral
factor. This is the order and counting part of residual restriction; the
change-of-actor survival theorem is a separate group-theoretic input.
-/

public section
open Subgroup Classical
namespace NoncentralChiefRefinement
variable {K : Type*} [Group K]

/-- The chief count is the sum of the indicators of its actual qualifying factors. -/
theorem ChiefSeries.noncentralTwoCount_eq_sum (s : ChiefSeries K) :
    s.noncentralTwoCount = ∑ i : Fin s.length,
      (if IsNoncentralTwo (s i.castSucc) (s i.succ) then 1 else 0) := by
  classical
  rw [ChiefSeries.noncentralTwoCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

/-- An exhibited noncentral binary chief interval gives a positive count. -/
theorem ChiefSeries.noncentralTwoCount_pos (s : ChiefSeries K)
    (h : ∃ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ)) :
    0 < s.noncentralTwoCount := by
  obtain ⟨i, hi⟩ := h
  let : Nonempty {i : Fin s.length // IsNoncentralTwo (s i.castSucc) (s i.succ)} := ⟨⟨i, hi⟩⟩
  exact Nat.card_pos

private theorem exists_refinement_count [Finite K] {n : ℕ} (f : Filtration K n)
    (m : Fin n → ℕ)
    (h : ∀ i, ∃ s : ChiefSeries K,
      s.head = f.term i.castSucc ∧ s.last = f.term i.succ ∧ m i ≤ s.noncentralTwoCount) :
    ∃ s : ChiefSeries K, s.head = f.term 0 ∧ s.last = f.term (Fin.last n) ∧
      (∑ i, m i) ≤ s.noncentralTwoCount ∧ (∀ i, ∃ j, s j = f.term i) := by
  induction n with
  | zero =>
    refine ⟨RelSeries.singleton _ (f.term 0), rfl, rfl, ?_, ?_⟩
    · simp
    · intro i
      exact ⟨0, congrArg f.term (Fin.ext (by omega))⟩
  | succ n ih =>
    let f' : Filtration K n := ⟨fun i => f.term i.castSucc, fun _ _ h => f.monotone h⟩
    obtain ⟨s, hs0, hs1, hsc, hs⟩ := ih f' (fun i => m i.castSucc) (fun i => h i.castSucc)
    obtain ⟨t, ht0, ht1, htc⟩ := h (Fin.last n)
    have hst : s.last = t.head := hs1.trans ht0.symm
    refine ⟨s.smash t hst, ?_, ?_, ?_, ?_⟩
    · exact (RelSeries.head_smash hst).trans hs0
    · exact (RelSeries.last_smash hst).trans ht1
    · rw [ChiefSeries.noncentralTwoCount_smash, Fin.sum_univ_castSucc]
      exact Nat.add_le_add hsc htc
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact ⟨Fin.last _, (RelSeries.last_smash hst).trans ht1⟩
      · obtain ⟨j, hj⟩ := hs i
        exact ⟨j.castLE (by simp), (RelSeries.smash_castLE hst j).trans hj⟩

/-- A binary indicator is earned by an actual noncentral chief interval in
its stratum. The hypotheses are local action and refinement facts, not a
prescribed total count. Every coarse term is retained. -/
theorem Filtration.exists_refinement_counting_surviving_strata [Finite K]
    {n : ℕ} (f : Filtration K n) (P : Fin n → Prop)
    (hsection : ∀ i, P i → IsNoncentralTwo (f.term i.castSucc) (f.term i.succ))
    (hrefine : ∀ s : ChiefSeries K, IsNoncentralTwo s.head s.last →
      ∃ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ)) :
    ∃ (s : ChiefSeries K) (ι : Fin (n + 1) →o Fin (s.length + 1)),
      (∀ i, s (ι i) = f.term i) ∧ ι 0 = 0 ∧ ι (Fin.last n) = Fin.last s.length ∧
      (∑ i, if P i then 1 else 0) ≤ s.noncentralTwoCount := by
  classical
  obtain ⟨s, hs0, hs1, hsc, hs⟩ := exists_refinement_count f
    (fun i => if P i then 1 else 0) (by
      intro i
      obtain ⟨t, ht0, ht1⟩ := exists_chiefSeries (f.term i.castSucc) (f.term i.succ)
        (f.monotone (Fin.castSucc_le_succ i))
      refine ⟨t, ht0, ht1, ?_⟩
      by_cases hi : P i
      · rw [if_pos hi]
        apply t.noncentralTwoCount_pos
        apply hrefine
        rw [ht0, ht1]
        exact hsection i hi
      · simp only [if_neg hi, Nat.zero_le])
  let j := fun i => (hs i).choose
  have hj : ∀ i, s (j i) = f.term i := fun i => (hs i).choose_spec
  let ι : Fin (n + 1) →o Fin (s.length + 1) :=
    ⟨j, fun i k hik => s.strictMono.le_iff_le.mp (by rw [hj, hj]; exact f.monotone hik)⟩
  refine ⟨s, ι, hj, ?_, ?_, hsc⟩
  · exact s.injective ((hj 0).trans hs0.symm)
  · exact s.injective ((hj (Fin.last n)).trans hs1.symm)

end NoncentralChiefRefinement
