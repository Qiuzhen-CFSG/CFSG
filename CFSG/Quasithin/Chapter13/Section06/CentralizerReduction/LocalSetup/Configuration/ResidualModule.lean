module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.Natural

/-!
# The residual quotient and checked natural module in 13.6

For a finite ambient group, an actual A₅ marking and its earlier action-kernel
identity suffice for every module assertion in the paragraph before 13.6.4:
the cubic quotient of Lᵥ, the natural direct-product map onto Vᵥ, the faithful
irreducible rank-two natural action on its literal checked image, the checked
commutator equality, and the ambient conjugate a centralizing Lᵥ.

The full vector stabilizer has order six; only its two-residual supplies the
cubic actor. Every checked image uses C_G(v) → C_G(v)/vLine v.

The configuration consumer can use `FlagMarking.residual_and_checked` and
`FlagMarking.checkedNaturalData`, together with `spanProductEquiv f.module`.
All premises are the marking and the original action-kernel field; the
constructions are independent of the separate flag-alignment calculation.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.926
and §B.3, printed p.83.
-/
