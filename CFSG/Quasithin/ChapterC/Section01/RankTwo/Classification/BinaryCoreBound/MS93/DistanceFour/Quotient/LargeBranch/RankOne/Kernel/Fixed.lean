module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Kernel.Fixed.Reduction

/-!
# Moving-span fixed-kernel elimination: the remaining geometric obligation

`Fixed.moving_fixed_eq_bot_of_flag_bound` proves the desired elimination
from the actual rank-one fixed-preimage bound `Fixed.FlagCoreBound`.
The bound is on core/U, with the two parabolics of the original projection
and flag. A bound on VStar/Z does not supply it.

The constructor of this bound from the large-intersection hypotheses of
MS93 (1993), (4.6.12), printed pp.910--912, remains to be proved. Consequently
this module does not yet assert the unconditional fixed-kernel elimination
or construct MovingKernelControl.
-/
