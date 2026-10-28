module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.Factors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.FaithfulClosure
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.Preimage
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors.SourceFactors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors.SourceAssembly

/-!
# The two-factor branch of the transvection argument

The actual coordinate-compatible B.1.8 factors are permuted by ambient
conjugation. A transvection occupies one factor, and its normal generation
forces the Sylow two-subgroup to interchange both. Sylow restriction and
a concrete S₃ × S₃ calculation then exclude every invariant subgroup of
order three in the normal closure.

For the literal source subgroup L₁=O²(N_LT(V₁)), two-perfectness proves
that L₁* normalizes each factor. Its marked local model supplies the order
restriction, and the three-rank bound places it inside K* as a three-group.
In the simple case L₁* is cubic; in the covered case the literal L₀* is
cubic. Both are T-invariant, giving the contradiction.

`source_two_factors_impossible` retains the full standing source setup
and derives the rank bound from quasithinness. The earlier compatible
local-model alternative is an explicit universal input. The actual
B.1.8 factors and their count two are the conditional branch inputs;
construction of those factors and final nonsolvability remain with the
Solvable parent.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.5, printed p.947 (PDF p.964).
-/
