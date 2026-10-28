module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Cases
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Reductions

/-!
# The order bound outside Δ₀

The checked action maps and common reductions for 16.4.9(1) are exported here.
The full theorem still requires three independent model arguments: exhaustiveness
of `OrderTwo.ResidualCentralizerAlternative`, the S₈ transposition contradiction,
and the M₁₂ cover and trivial-cover contradictions. The case predicates are
specifications of those obligations, not proofs of them.

Once these inputs are proved, `StandardSetup.orderTwoOutsideDeltaZero_of_local`
transports the normalized order assertion to every relative Sylow choice.
Final assembly of that order assertion belongs to this module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.4.9(1), printed p.1189.
-/
