/-
Authors: Tianjiao Nie
-/

module

public import Submission.FeitThompson.BGsection1.theorem_1_18

open scoped Pointwise

public section

/-
**Kind**: Theorem
**Note**: Corollary 1.19
**Stmt**:
Let $G$ be a group.
(a) If $S$ is a cyclic Sylow subgroup of $G$, then either $S \cap G' = 1$ or $S \subset G'$.
(b) If $G$ is a $Z$-group, then $G'$ is a Hall subgroup of $G$.
-/

-- Corollary 1.19(a)
public theorem corollary_1_19_a {G : Type*} [Group G] [Finite G] :
    ∀ (p : ℕ) [Fact p.Prime],
      ∀ S : Sylow p G,
        IsCyclic (↥(S : Subgroup G)) →
          ((S : Subgroup G) ⊓ derivedSubgroup G = ⊥) ∨ (S : Subgroup G) ≤ derivedSubgroup G := by
  intro p _hp S hcyc
  simpa [derivedSubgroup] using
    (sylow_inf_commutator_eq_bot_or_le_commutator (G := G) p S hcyc)

-- Corollary 1.19(b)
public theorem corollary_1_19_b {G : Type*} [Group G] [Finite G] :
    IsZGroup G → ∃ π : Set Nat.Primes, IsHallSubgroup π (derivedSubgroup G) := by
  intro hZ
  simpa [derivedSubgroup] using
    (exists_isHallSubgroup_commutator_of_isZGroup (G := G) hZ)


end
