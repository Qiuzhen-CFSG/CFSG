module

public import Theory.SpecificGroups.G2Even.TwoRank.AutomorphismBound
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Descent
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Cocycle

/-!
# The full automorphism two-rank bound for even G₂

The proved cocycle calculation and coefficient-fixed descent supply the
structural inputs to the semilinear rank argument. Inner-field coverage then
gives the bound for every automorphism, including outer field automorphisms.
The second theorem transports it to the actual derived group.

Source: Aschbacher–Smith 16.1.4(4), 16.1.7(3a), and 16.3.9.
-/

public section

namespace Atlas.G2.EvenTwoRank
open Theory.GroupTheory LieAutomorphismExtensions EvenFieldFixedResidual

variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The full automorphism group has two-rank at most three times the field degree. -/
theorem source_automorphism_two_rank_le {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) :
    primeRank 2 (MulAut (Model F)) ≤ 3 * n := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < n by omega)
  exact automorphism_two_rank_le F
    (cocycle_eq_coboundary hq)
    (fun σ _ => ⟨coefficientFixedEquiv σ⟩)
    hn hF (semilinearAction_surjective hq)

/-- The same source bound for automorphisms of the genuine derived subgroup. -/
theorem source_derived_automorphism_two_rank_le {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) :
    primeRank 2 (MulAut (commutator (Model F))) ≤ 3 * n := by
  rw [primeRank_equiv 2 (derivedAutEquiv F hn hF)]
  exact source_automorphism_two_rank_le F hn hF

end Atlas.G2.EvenTwoRank
