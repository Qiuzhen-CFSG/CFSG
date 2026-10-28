module

public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Flags

/-!
# A finite marked flag with a prescribed noncentral count

Three noncentral chief intervals separated by two arbitrary central
intervals give a complete chief flag with exactly three noncentral factors.
Finite invariant-subspace lattices supply refinements of the central gaps;
all their subintervals remain central. Concatenating these with the three
actual chief intervals computes the count. The source71 application retains
the literal actor and does not require the carrier to lie in that actor.
-/

@[expose] public section
open Representation
namespace BinaryLinearThree.ParabolicCyclic.ChiefCounts

variable {G M : Type*} [Group G] [AddCommGroup M] [Module (ZMod 2) M]
  {ρ : Representation (ZMod 2) G M}

theorem hasCount_of_series_count_eq {n : ℕ}
    (s : Series ρ) (hhead : s.head = ⊥) (hlast : s.last = ⊤)
    (I : Finset (Fin s.length))
    (hI : ∀ i, i ∈ I ↔ ¬ Central (s i.castSucc) (s i.succ))
    (hcard : I.card = n) : HasCount ρ n := by
  refine ⟨s, hhead, hlast, ?_⟩
  exact (s.count_eq_card I hI).trans hcard

theorem hasCount_three_of_series
    (s : Series ρ) (hhead : s.head = ⊥) (hlast : s.last = ⊤)
    (i₁ i₂ i₃ : Fin s.length)
    (hdistinct : i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃)
    (hnoncentral : ∀ i, i = i₁ ∨ i = i₂ ∨ i = i₃ ↔
      ¬ Central (s i.castSucc) (s i.succ)) : HasCount ρ 3 := by
  let I : Finset (Fin s.length) := {i₁, i₂, i₃}
  have hI : ∀ i, i ∈ I ↔ ¬ Central (s i.castSucc) (s i.succ) := by
    intro i
    simpa [I, or_assoc, or_left_comm, or_comm] using hnoncentral i
  have hcard : I.card = 3 := by
    simp [I, hdistinct.1, hdistinct.2.1, hdistinct.2.2]
  exact hasCount_of_series_count_eq s hhead hlast I hI hcard

/-- Every finite invariant interval has an actual chief refinement. -/
theorem exists_interval_series [Finite M] (A B : Subrepresentation ρ) (hAB : A ≤ B) :
    ∃ s : Series ρ, s.head = A ∧ s.last = B := by
  obtain ⟨a, ha, n, hn, hstep⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le hAB
  exact ⟨⟨n, fun i => a i, fun i => hstep i i.isLt⟩, ha, hn⟩

/-- A central interval contributes no noncentral factors in any refinement. -/
theorem exists_central_series [Finite M] (A B : Subrepresentation ρ)
    (hAB : A ≤ B) (hc : Central A B) :
    ∃ s : Series ρ, s.head = A ∧ s.last = B ∧ s.count = 0 := by
  obtain ⟨s, h0, h1⟩ := exists_interval_series A B hAB
  refine ⟨s, h0, h1, ?_⟩
  apply Nat.card_eq_zero.mpr
  left
  refine ⟨fun i => i.property ?_⟩
  intro g v hv
  exact (h0 ▸ s.head_le i.val.castSucc) (hc g v ((h1 ▸ s.le_last i.val.succ) hv))

/-- One genuine noncentral chief interval contributes one. -/
theorem exists_noncentral_chief_series (A B : Subrepresentation ρ)
    (hAB : A ⋖ B) (hc : ¬ Central A B) :
    ∃ s : Series ρ, s.head = A ∧ s.last = B ∧ s.count = 1 := by
  let s : Series ρ := ⟨1, ![A,B], by intro i; fin_cases i; exact hAB⟩
  refine ⟨s, rfl, rfl, ?_⟩
  apply (s.count_eq_card {0} ?_).trans (by simp)
  intro i
  fin_cases i
  simpa [s] using hc

/-- Concatenate counts on two literal neighboring intervals. -/
theorem exists_series_count_join {A B C : Subrepresentation ρ} {m n : ℕ}
    (hAB : ∃ s : Series ρ, s.head = A ∧ s.last = B ∧ s.count = m)
    (hBC : ∃ s : Series ρ, s.head = B ∧ s.last = C ∧ s.count = n) :
    ∃ s : Series ρ, s.head = A ∧ s.last = C ∧ s.count = m+n := by
  obtain ⟨s, hs0, hs1, hs⟩ := hAB
  obtain ⟨t, ht0, ht1, ht⟩ := hBC
  have hst : s.last = t.head := hs1.trans ht0.symm
  exact ⟨s.smash t hst, (RelSeries.head_smash hst).trans hs0,
    (RelSeries.last_smash hst).trans ht1, (s.count_smash t hst).trans (by rw [hs, ht])⟩

/-- Three noncentral chief intervals separated by arbitrary central gaps.
The source supplies only the five actual sections, not a complete chief flag. -/
theorem hasCount_three_of_five_intervals [Finite M]
    (P₁ P₂ P₃ P₄ : Subrepresentation ρ)
    (h₀ : (⊥ : Subrepresentation ρ) ⋖ P₁) (h₁ : P₁ ≤ P₂)
    (h₂ : P₂ ⋖ P₃) (h₃ : P₃ ≤ P₄) (h₄ : P₄ ⋖ (⊤ : Subrepresentation ρ))
    (hc₀ : ¬ Central ⊥ P₁) (hc₁ : Central P₁ P₂)
    (hc₂ : ¬ Central P₂ P₃) (hc₃ : Central P₃ P₄)
    (hc₄ : ¬ Central P₄ ⊤) : HasCount ρ 3 := by
  have h01 := exists_series_count_join (exists_noncentral_chief_series ⊥ P₁ h₀ hc₀)
    (exists_central_series P₁ P₂ h₁ hc₁)
  have h012 := exists_series_count_join h01 (exists_noncentral_chief_series P₂ P₃ h₂ hc₂)
  have h0123 := exists_series_count_join h012 (exists_central_series P₃ P₄ h₃ hc₃)
  simpa only [HasCount, Nat.add_zero, Nat.reduceAdd] using
    exists_series_count_join h0123 (exists_noncentral_chief_series P₄ ⊤ h₄ hc₄)

end BinaryLinearThree.ParabolicCyclic.ChiefCounts
