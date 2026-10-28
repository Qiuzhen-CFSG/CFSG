module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Split
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Sylow

/-!
# The complete pure-vector stabilizer family

For the actual natural-plus-dual coordinate action in degrees four and five,
the pure-vector stabilizer equals its embedded two-residual and is a split
extension of its elementary line radical by GL_(n−1)(2). The radical is its
intrinsic two-core. The quotient acts as the full linear group on ann(x),
compatibly with X/span(x). The commutator spaces are X and ann(x).

For every supplied Sylow T of the automorphism group, the natural-summand
normalizer T₁ fixes exactly one natural line, and T₁ is the Sylow centralizer
of every nonzero vector in that line. No fixed-line or parabolic conclusion
is assumed, and no adapted nonsingular-pair theorem is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(3),
printed pp.389–390. Existence of `CoordinateAction` is a separate model
construction; it is the sole action input here.
-/
