module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Basic
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryCore
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryModule
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryModule.IntersectionCommutator
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Assembly

/-!
# Marked parabolic calculations for Section 12.8

All seven clauses of 12.8.9 and all six clauses of 12.8.10 are proved from
precise preceding 12.8.1–8 inputs. `binary_source_parabolic_calculations`
assembles generation and relative normality, the actual residual and core
products, the literal natural tensor quotient with its complementary marked
images and fixed/moved spaces, and the hat/tilde action and displacement clauses.
`binary_source_center_calculations` discharges every 12.8.9 premise in the
center calculation, including the canonical fixed-space pullback and the two
original action kernels. It gives the full center/intersection/kernel chain,
the literal moved-rank bound, and the conditional internal multiplication
equivalence with L-centralization. The original g and Z(U)^g are retained.

The section assembly retains the earlier flag, action, commutator-form and
local-kernel inputs. Rank two uses full LT-action; full L-action is required
only in higher rank. The printed H-span is corrected to the G₂-span proved
in the source, and the original antecedent Z(U)^g ≤ U is preserved.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Lemmas 12.8.9–10, printed pp.852–854.
-/
