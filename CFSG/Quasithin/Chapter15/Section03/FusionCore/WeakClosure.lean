module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Assembly
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.CoordinateModel
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.SourceAssembly

/-!
# The weak-closure argument of 15.3.46–47

The earlier-source interface retains the definite plane in the actual
quadratic space, the local module generated from `Z`, the two-residual
uniqueness dichotomy, and the centralizer bound of 15.3.45(3).

The proved group-theoretic deductions take centralization of the actual
`W₀(T,V)` to positivity of `w(G,V)`, centralization of every conjugate in
`M`, and the full normalizer bound via Frattini and 15.3.2(4).
An independent displacement argument proves the nonsingularity assertion
used in 15.3.47.

`lemma_15_3_46_of_earlier_inputs` and `lemma_15_3_47_of_earlier_inputs`
assemble all five clauses and the commutator alternative. They construct
the compatible coordinate model, orbit and Sylow data, and discharge both
cases of `W₀(T,V) ≤ C_G(V)`. Their only inputs are the genuine natural
orthogonal action, the definite plane, and `EarlierFusionInputs`; the
parent section assembly remains responsible for those earlier conclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1141.
-/
