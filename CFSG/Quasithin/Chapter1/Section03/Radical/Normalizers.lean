module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.SinglePrime
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Assembly

/-!
# Characteristic normalizers of radical members

The imported assembly proves C(G,R) ≤ N_G(L) for R = O₂(Ξ_p(L)T),
the normalizer claim in Proposition 1.3.8, printed pp.512–513. It combines
the single-prime omega argument, the actual residual normalizer, solvable
Thompson factorization, the A.3.12 embedding elimination, and the marked
L₃(5) parabolic signalizer theorem. Characteristic subgroups lie inside R,
and all component normality is relative to the specified overgroup.

The earlier universal A.3, B.2.16 and 1.2.7 results remain explicit
parameters. All construction-specific premises are discharged. A second
export gives C(G,O₂(XT)) ≤ N_G(X) for every X ∈ Ξ*_rad(G,T).
-/
