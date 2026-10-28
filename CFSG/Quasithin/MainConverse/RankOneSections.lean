module

public import CFSG.Quasithin.MainConverse.RankOneSections.Linear
public import CFSG.Quasithin.MainConverse.RankOneSections.Unitary

/-!
# Proper simple sections of the rank-one alternatives

The linear calculation uses the exact `ClassicalGroup.IsPSL` model and
proves the proper-K clause for every finite field order. It therefore covers
the binary and Fermat–Mersenne alternatives in Aschbacher–Smith,
Theorem 0.1.2, printed p.4, repeated as Theorem 0.1.1 on p.482.

The unitary reduction uses the actual injection PSU₃(q) → PSL₃(q²),
preserving the coefficient-field convention. Its conclusion is conditional
on the separate proper-K theorem for PSL₃(q²); that premise remains to be
discharged before asserting the complete rank-one converse.
-/
