module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic.Choose
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite descending subgroup filtrations

An antitone sequence of subgroups with finite initial term stabilizes at its
intersection: choose, for every element outside the intersection, a stage
excluding it and take the maximum of these finitely many stages. If the
intersection is trivial, a nontrivial subgroup contained in the first term has
a unique last positive radius of containment.

This supplies the finite descending-chain argument in Aschbacher--Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
Lemma F.7.3(8) and Definition F.7.8. Proving that the ball-kernel intersection
is trivial is a separate application-specific obligation.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- A descending subgroup filtration with finite initial term stabilizes at
its intersection, even when the ambient group is infinite. -/
public theorem finite_filtration_stabilizes (K : ℕ → Subgroup G)
    [Finite (K 0)] (hK : Antitone K) :
    ∃ N : ℕ, ∀ n, N ≤ n → K n = ⨅ m, K m := by
  classical
  let _ := Fintype.ofFinite (K 0)
  have hex : ∀ g : K 0, ∃ n : ℕ, (g : G) ∈ K n → (g : G) ∈ ⨅ m, K m := by
    intro g
    by_cases hg : (g : G) ∈ ⨅ m, K m
    · exact ⟨0, fun _ => hg⟩
    · have hfail : ∃ n, (g : G) ∉ K n := by
        simpa only [mem_iInf, not_forall] using hg
      obtain ⟨n, hn⟩ := hfail
      exact ⟨n, fun h => (hn h).elim⟩
  choose f hf using hex
  refine ⟨Finset.univ.sup f, fun n hn => le_antisymm ?_ (iInf_le K n)⟩
  intro g hg
  let g₀ : K 0 := ⟨g, hK (Nat.zero_le n) hg⟩
  exact hf g₀ (hK (le_trans (Finset.le_sup (Finset.mem_univ g₀)) hn) hg)

/-- Trivial intersection gives a positive stage after which every term is trivial. -/
public theorem finite_filtration_eventually_bot (K : ℕ → Subgroup G)
    [Finite (K 0)] (hK : Antitone K) (hbot : (⨅ m, K m) = ⊥) :
    ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n → K n = ⊥ := by
  obtain ⟨N, hN⟩ := finite_filtration_stabilizes K hK
  refine ⟨N + 1, Nat.zero_lt_succ N, fun n hn => ?_⟩
  exact (hN n (by omega)).trans hbot

/-- A nontrivial subgroup lying in the first term of a filtration that vanishes
has a last positive radius of containment. The final equivalence characterizes
that radius uniquely. -/
public theorem exists_last_filtration_radius (K : ℕ → Subgroup G) (hK : Antitone K)
    (V : Subgroup G) (hV : V ≠ ⊥) (hfirst : V ≤ K 1)
    (hvanish : ∃ N, K N = ⊥) :
    ∃ b : ℕ, 0 < b ∧ V ≤ K b ∧ ¬ V ≤ K (b + 1) ∧
      ∀ n, V ≤ K n ↔ n ≤ b := by
  classical
  have hex : ∃ n, ¬ V ≤ K n := by
    obtain ⟨N, hN⟩ := hvanish
    exact ⟨N, fun h => hV (le_bot_iff.mp (hN ▸ h))⟩
  let c := Nat.find hex
  have hc : ¬ V ≤ K c := Nat.find_spec hex
  have hbefore : ∀ n < c, V ≤ K n := by
    intro n hn
    exact not_not.mp (Nat.find_min hex hn)
  have htwo : 1 < c := by
    by_contra h
    exact hc (hfirst.trans (hK (by omega)))
  refine ⟨c - 1, by omega, hbefore _ (by omega), ?_, ?_⟩
  · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ c)] using hc
  · intro n
    constructor
    · intro hn
      by_contra hle
      exact hc (hn.trans (hK (by omega)))
    · intro hn
      exact hbefore n (by omega)

end Subgroup
