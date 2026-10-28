module

public import GorensteinWalter.Section2.ComplementConjugacy
public import Theory.GroupTheory.Commutator.ActionTriviality
public import FeitThompson.GroupAction.Cardinalities
public import Theory.GroupTheory.Commutator.PTimesQ

/-!
# Thompson's P × Q lemma

This preserves the ambient-subgroup form of Kurzweil–Stellmacher 8.2.8
used by Bender's Statement 1.1. A p-group P and a p-prime group Q commute
and normalize a p-group B. If Q centralizes C_B(P), it centralizes B.
The shared Theory proof inducts on |B|, uses properness of [B,P] and the
three-subgroups lemma, then applies coprime commutator idempotence.

The public theorem and prior imports are retained. Its implementation now
lives in Theory.GroupTheory.Commutator.PTimesQ so other developments can
reuse this general p-group result without a campaign dependency.
-/

namespace GorensteinWalter.ThompsonPQ
universe u

/-- **Thompson's P × Q lemma** (Kurzweil--Stellmacher 8.2.8), in the
ambient-subgroup form needed by Bender's Statement 1.1.

Here `P` and `B` are `p`-groups, `Q` has order prime to `p`, `P` and `Q`
commute, and both normalize `B`.  The fixed-point containment is written as
`C_B(P) ≤ C_G(Q)`. -/
public theorem thompson_p_times_q
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P Q B : Subgroup G)
    (hPp : IsPGroup p P) (hBp : IsPGroup p B)
    (hQcop : Nat.Coprime p (Nat.card Q))
    (hPB : P ≤ Subgroup.normalizer (B : Set G))
    (hQB : Q ≤ Subgroup.normalizer (B : Set G))
    (hPQ : ⁅P, Q⁆ = ⊥)
    (hfixed : B ⊓ Subgroup.centralizer (P : Set G) ≤
      Subgroup.centralizer (Q : Set G)) :
    ⁅B, Q⁆ = ⊥ := by
  exact Subgroup.p_times_q_centralizer P Q B hPp hBp hQcop hPB hQB hPQ hfixed

end GorensteinWalter.ThompsonPQ
