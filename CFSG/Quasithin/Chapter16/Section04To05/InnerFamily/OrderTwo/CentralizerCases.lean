module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Cases
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Reductions
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.InnerExclusions

/-!
# Residual-centralizer case analysis for 16.4.9(1)

The common model transport and the M₁₁ and Suzuki exclusions are proved.
The faithful model action preserves both the actual residual image and the
outer involution. A bound of twice an odd number on its pointwise fixer
suffices for case (I), allowing the abelian odd residual in small fields.

Exhaustiveness of `ResidualCentralizerAlternative` still requires the
remaining (E2) family calculations. In the S₈ and M₁₂ cases those must
identify the full centralizer with E₄ and establish all model markings.
An abstract fixed-subgroup isomorphism does not supply these calculations.
Final assembly of that alternative belongs here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.1170–1172 and the proof of 16.4.9(1) on p.1189.
-/
