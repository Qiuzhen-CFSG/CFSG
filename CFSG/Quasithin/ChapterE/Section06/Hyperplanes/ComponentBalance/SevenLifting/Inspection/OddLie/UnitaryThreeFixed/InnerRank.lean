module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie.UnitaryThreeFixed.Inputs
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank

/-!
# Inner PSU₃ involutions in the odd-prime inspection

The intrinsic calculation applies to the actual projective unitary model,
with its arbitrary nondegenerate Hermitian form and inherited simplicity.
Its proof lifts centralizers through the scalar kernel and embeds the first
commutator of the covering centralizer in SL₂(p). The result includes p = 3.

Source: Aschbacher–Smith E.6.18, printed p.252, Theorem C, printed p.33,
and A.3.21(a), printed p.55.
-/

public section

open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie

/-- The complete inner-involution rank input for the odd-prime unitary branch. -/
theorem innerDerivedThreeRank_unitary {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    UnitaryThreeFixed.InnerDerivedThreeRank p := by
  let : Fact p.Prime := ⟨hp⟩
  intro E hfield hfinite J hsimple hcard hconj k hk
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := hsimple
  exact Matrix.SU3.InnerThreeRank.inner_involution_derived_rank p ho E J hcard hconj k hk

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie
