module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.FiveFlags
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OvergroupLift
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.SourceAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.FiveElimination
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Reduction

/-!
# Parabolic reduction in Aschbacher–Smith 13.8.25

`Parabolics.source_parabolic_reduction` proves n = 4 from the prescribed
K/O₂(K) ≃ Lₙ(2), 3 ≤ n ≤ 5, and explicit earlier source inputs. It returns
either the triple-cover case with H* ≃ L₄(2), T* = T*∩K*, H∩M = L₁T and
the two marked end nodes, or the ordinary A₆ case with the compatible
H* ≃ S₈ action, T*∩K* < T*, and the actual marked middle-node parabolic.

The source natural actions construct the flag placements and residual
identities. The dimension-five contradictions use constructed Levi
overgroups; the ordinary inner degree-four contradiction uses an actual
PSL₃(2) local component whose overgroup belongs to Hz. Component kernels,
relative normality and the original subgroup markings are retained.
No critical-denominator restriction is imposed, so both cases of 13.8.8
are covered. The orthogonal exclusion, natural-module conclusion and
H = G₁ belong to the downstream completion of 13.8.25.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.25, printed pp.959–960 (PDF pp.976–977).
-/
