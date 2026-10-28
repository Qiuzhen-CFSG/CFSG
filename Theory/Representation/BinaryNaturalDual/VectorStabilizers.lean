module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Modules
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Outer
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.ResidualActions

/-!
# Natural-plus-dual vector stabilizers

This entry point exposes the complete pure and nonsingular stabilizer families
for an explicit coordinate action of the actual automorphism group. The pure
stabilizer is a split elementary extension with its intrinsic two-core,
quotient actions and fixed-Sylow marking. The nonsingular stabilizer is the
actual automorphism group in one lower dimension, with its outer involutions,
two-residual, natural/dual complementary actions and exact fixed and
commutator spaces. Every stabilizer Sylow contains an outer involution.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(3–4),
printed pp.389–390; the corrected nonsingular statement chooses its outer
involution independently of the Sylow marking of the pure vector.
-/
