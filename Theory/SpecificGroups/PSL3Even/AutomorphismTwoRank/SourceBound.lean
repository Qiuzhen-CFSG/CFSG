module

public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.StandardRank

/-!
# Two-rank of the full binary PSL₃ automorphism group

Over fields larger than two, the proved linear–field–graph coverage identifies
the full automorphism group with the standard subgroup, whose two-rank is at
most twice the field degree. The binary endpoint uses its actual PGL₂(7)
comparison. Inner automorphisms attain the same bound.

Source: GLS3, Theorem 2.5.12(a), and Aschbacher–Smith 16.3.9, printed p.1180.
-/

public section
open Theory.GroupTheory
namespace Matrix.PSL3Even

/-- The full automorphism group has two-rank exactly twice the binary field degree. -/
theorem automorphism_two_rank_eq (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    primeRank 2 (MulAut (ProjectiveSpecialLinearGroup (Fin 3) F)) = 2 * n := by
  by_cases h1 : n = 1
  · subst n
    simpa using automorphism_two_rank_eq_of_card_two F (by simpa using hF)
  have hlarge : 1 < n := by omega
  apply le_antisymm _ (le_automorphism_two_rank F hn hF)
  have hb := PSL3.OuterSolvable.standard_two_rank_le_of_two_power_card F hlarge hF
  rw [AutomorphismCoverage.standard_eq_top F hlarge hF] at hb
  rwa [primeRank_equiv 2 (Subgroup.topEquiv)] at hb

end Matrix.PSL3Even
