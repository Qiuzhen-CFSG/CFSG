module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.ChiefCases
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Residual

/-!
# Fixed-space and residual reductions toward 15.3.23

The intrinsic six-chief-factor exclusion uses the central four and the actual
natural summand in C.1.34(4). A separate transport lemma connects its central
omega bound to 15.3.8 when the local Sylow embedding has been constructed.
The residual calculation proves O²(Y_C O₂(L)) = Y_C and L ≤ N_G(Y_C)
from S-invariance of Y_C, giving the normalizer contradiction in choice (2).

The source extension calculation for V ≤ U_L C_WL(L), the noncentrality
of [V,Y_L], residual exchange and the natural line geometry remain to be
constructed. In particular this module does not assert elimination of either
choice of Hypothesis 15.3.10 or of C.1.34(5). FirstThreeCases retains the full
compatible action data required by the independent core-action argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.23, printed pp.1128–1129; C.1.34, printed pp.136–137.
-/
