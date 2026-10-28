module

public import Theory.SpecificGroups.PSL3Four.GraphFieldFixedSylow
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Normalization.SylowTransvection.Transfer

/-!
# The projective fixed-Sylow input for the cover transvection

The intrinsic matrix theorem proves that graph-field fixed points preserve
Sylow maximality for the supplied invariant Sylow subgroup of PSL₃(4).
This discharges the projective input of the central-cover transfer, retaining
the prepared ambient Sylow subgroup throughout that transfer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the graph-field
branch of 16.4.9(2), printed p.1191. The source-level transvection assembly
remains in the SylowTransvection owner.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.GraphField.SylowTransvection

/-- The actual graph-field action satisfies the fixed-Sylow assertion required
by the cover transvection transfer. -/
theorem projectiveFixedSylow : ProjectiveFixedSylow :=
  Matrix.PSL3Four.GraphFieldFixedSylow.exists_fixedSylow

end CFSG.Quasithin.Chapter16.Intersections.GraphField.SylowTransvection
