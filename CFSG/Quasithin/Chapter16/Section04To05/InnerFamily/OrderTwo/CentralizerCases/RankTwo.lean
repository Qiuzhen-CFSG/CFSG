module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.InnerExclusions
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.RankTwo.GraphField

/-!
# Rank-two residual-centralizer calculations

The graph-field export transports the actual residual and its full pointwise
fixer to the specified PSL₃(4) model, retaining any central covering kernel.
The allowed concrete fixer bound then gives a Sylow subgroup of order two
in the residual centralizer.

Exhaustiveness over the rank-two catalogue still requires the other linear,
symplectic and exceptional fixer calculations, including the small derived
and Tits endpoints. In particular the A₆ endpoint must retain the earlier
16.4.6 exclusion. This module does not yet assert that exhaustive theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4 and the proof of 16.4.9(1), printed pp.1171 and 1189.
-/
