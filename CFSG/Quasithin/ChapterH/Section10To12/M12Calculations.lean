module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.AmbientInput
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Residual

/-!
# M₁₂ permutation-heart calculations for H.11

The native ten-dimensional heart has involution displacement four, and a
marked element of order three has displacement six. These calculations are
transported to the given solvable residual using its actual group and module
equivalences. In particular the ambient parameter satisfies `m ≤ 4`.

The ambient-extension construction, outer displacement, elementary-subgroup
calculations, quaternion fixed-space obstruction, and uniform odd-prime lower
bound remain separate obligations. `AmbientExtension` specifies the actual
equivariant construction needed by the outer calculations; no existence of
that witness or complete H.11.1 theorem is asserted by this module yet.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.11,
printed pp.392–393. The rank-four assertion must be distinguished from the
rank-three residual case; no uniform equality `m₂ = 4` is asserted here.
-/
