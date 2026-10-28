module

public import CFSG.Quasithin.ChapterE.Section04.MathieuBounds.M12
public import CFSG.Quasithin.ChapterE.Section04.MathieuBounds.SmallQuotients

/-!
# The three Mathieu module bounds of E.4.3

This umbrella exports the source bounds in
`CFSG.Quasithin.ChapterE.ValueBound.MathieuBounds`:

* `moduleA_le_two_of_m12` proves (1) for L/Z(L) ≃ M₁₂.
* `moduleA_le_three_of_m22_or_m24` proves (2), with separate M₂₂ and M₂₄
  endpoints as well.
* `moduleA_le_three_of_isM23Code_or_isM23Cocode` proves (3) for the actual
  code or cocode module, with separate and native-representation endpoints.

The first two clauses retain the full finite ambient, trivial-two-core,
quasisimple generalized-Fitting, faithful binary representation and strict
Sylow fixed-space hypotheses. The genuine central-quotient identifications
supply the needed generating families, including the permitted covers and
outer extensions. The rank budgets are two for the M₁₂ pair and three for
the M₂₂ pair and M₂₄ triple. The last clause follows by restriction of the
actual M₂₄ code and cocode; it has no additional bound or local-model premise.

These theorems use the proved generating-family bound for intrinsic local
two-core quotients S₃ and S₅. They do not assert the literal general E.4.2
statement or complete the other results of Section E.4.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.3,
printed pp.241–242 (PDF pp.252–253).
-/
