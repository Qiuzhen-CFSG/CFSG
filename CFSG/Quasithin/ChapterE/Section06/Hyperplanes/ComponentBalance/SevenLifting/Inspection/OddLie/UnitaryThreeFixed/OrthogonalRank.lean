module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie.UnitaryThreeFixed.Inputs
public import Theory.SpecificGroups.SU3.TernaryOrthogonalThreeRank

/-!
# The ternary orthogonal rank input for unitary involution inspection

The actual determinant-one orthogonal matrix group has three-rank at most
one over every odd prime field, including the field of order three. The
proof uses its index-two PSL₂ subgroup and cyclic Sylow three-subgroups;
the small fields are covered directly by the exact orthogonal order.

This discharges `OrthogonalThreeRank` for the outer involution branch of
the unitary-three inspection. Source: Aschbacher–Smith E.6.18, printed
p.252, and Theorem C, printed p.33; GLS3 §§2.7 and 4.3.
-/

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie.UnitaryThreeFixed

/-- The orthogonal rank input, with no restriction excluding characteristic three. -/
public theorem orthogonalThreeRank {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    OrthogonalThreeRank p := by
  intro K _ _ hK
  exact BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.TernaryOrthogonal.primeRank_three_le_one
    hp ho hK

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie.UnitaryThreeFixed
