module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.QuasisimpleAction
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.ResidualAction

/-!
# Small overgroups in the proof of 8.2.8(1)

The full-action cocode branch is proved from its earlier source action and
quasisimple quotient, with an actual Sylow subgroup and relative normality.
For all branches, action-image containment lifts to L_U = K_U through the
literal kernel, whose centrality modulo O₂(K_U) is proved from quasisimplicity. The dihedral setup also has the constructed action on
X = O²(I), P = O₂(I), and P/U, with the quotient kernel retained.

The marked rank-four overgroup exclusion, its odd-prime rank deductions,
and the compatible F₁₆ multiplicity-space inspection are not yet proved.
Thus this module does not assert the full Proposition 8.2.8(1). Final
assembly remains here after those independent model arguments are supplied.
Earlier conclusions 8.2.2–7 and 8.2.8(2–6) remain the responsibility of the
Normalizer owner. In particular the corrected tensor convention in
TensorDimension must be used, and the code branch cannot be discarded by
the inconsistent printed binary tensor formula.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final three
paragraphs proving Proposition 8.2.8(1), printed p.719 (PDF p.736).
-/
