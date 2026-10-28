module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Lifting
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Transport
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Assembly

/-!
# Cubic blocks in the residual involution argument

`exists_source_cubic_blocks` constructs both cubics from the genuine earlier
actions, assigns them to the actual order-32 local planes, and proves their
singular commutator lines and affine fusion reductions. Coprime fixed-point
lifting also places each plane directly in its corresponding block.

The compatible tensor coordinates and the proved intrinsic census give an
actual `BlockCensus` for each block, with orbit sizes 9, 6, 12 and 36 and both
inside orbits spanning `V`. Both E64 blocks lie in the residual Sylow group.
Only the permitted earlier action, center, fixed-lift, marking and Sylow
inputs remain explicit. The independent moving-normalizer calculation and
the final two-class cover of 15.3.61(2) belong to the parent assembly.

Source: Aschbacher–Smith, 15.3.54 and 15.3.61(2), pp.1146,1150–1151.
-/
