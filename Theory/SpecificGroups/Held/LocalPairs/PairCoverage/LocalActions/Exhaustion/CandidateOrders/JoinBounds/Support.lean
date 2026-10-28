module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Support

/-!
# Checking the permutation-image bounds for the Held joins

Boolean checks on natural-number functions certify pointwise permutation
identities, without repeatedly reducing equality decisions on `Fin`. The
faithful defining representation then transfers a bound on a subgroup of the
symmetric group to the actual join of the literal candidate closures.

Sources: the cyclic-series counting argument in `CandidateOrders.Support`;
the fixed ATLAS carrier and `LocalActions/source/Explore.g`.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.JoinBounds

/-- A kernel-reducible bounded check, with no intermediate list of letters. -/
def checkBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f n && checkBelow n f

theorem checkBelow_spec {n : ℕ} {f : ℕ → Bool} (h : checkBelow n f = true) :
    ∀ x < n, f x = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hn, ht⟩ := Bool.and_eq_true_iff.mp h
    intro x hx
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx) with hx | rfl
    · exact ih ht x hx
    · exact hn

theorem eq_of_check (f g : ℕ → ℕ)
    (h : checkBelow 2058 (fun x => f x == g x) = true)
    (x : ℕ) (hx : x < 2058) : f x = g x := by
  exact beq_iff_eq.mp (checkBelow_spec h x hx)

/-- Transport an upper bound through the faithful literal representation. -/
theorem card_le_of_generator_images (i : Bool) (j : Fin 2)
    (K : Subgroup (Equiv.Perm (Fin 2058)))
    (ho : ∀ k, representation (evalLocalWord i (oddWord i j k)) ∈ K)
    (ht : ∀ k, representation (evalLocalWord i (twoWord i j k)) ∈ K) :
    Nat.card (candidateProduct i j) ≤ Nat.card K := by
  rw [← Subgroup.card_map_of_injective representation_injective]
  apply Subgroup.card_le_of_le
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sup_le
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    exact ho k
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    exact ht k

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.JoinBounds
