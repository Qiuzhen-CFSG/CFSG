module

public import Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics.CoreCentralizer.Reduction

/-!
# Higher-unitary parabolic two-core centralizers

The checked flag-kernel construction and projective centralizer reduction are
re-exported here. They prove normality, the two-group property, and a reduction
to the scalar-shear matrix calculation for the literal geometric parabolic.

The general matrix calculation remains to be proved in the two cases
`Wᗮ = W` and `Wᗮ ≠ W`. Thus the available bound still has an explicit matrix
calculation premise; this module does not yet assert GLS3 2.6.5(e) for all
higher-unitary parabolics. Final assembly belongs here, above the independent
matrix branches and their common `Reduction` module.

Source: GLS3 2.6.5(e), `refs/KGroup/GLS3/chapter2.tex`, and Aschbacher--Smith
B.1.13, printed p.74 (PDF p.85) of `refs/quasithin.pdf`.
-/
