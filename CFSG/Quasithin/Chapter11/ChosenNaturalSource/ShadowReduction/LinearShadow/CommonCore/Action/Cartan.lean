module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Residual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Choice
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Coordinates
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Line
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Line
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Classification
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Single

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Dichotomy

/-!
# Cartan and line calculations for the original chosen natural module

The exact 11.0.4 residual clauses and actual odd Hall group put D₀ in L
and choose a compatible Cartan. The natural quotient calculation identifies
its fixed space on Z with C_Z(K). Local uniqueness eliminates C_Z(L),
C_V(L) and C_T(L), so the literal orbit ⟨Z^L⟩ is fully moved and fixed-free.

B.5.1(3) then gives homogeneous coordinates with the original natural seed
as every constituent. Inner flag uniqueness and the common scalar on the
first line prove the Cartan dichotomy for the whole orbit, retaining all
multiplicities. The source movement excludes the fixed alternative, giving
C_{V_H}(K)=1. The faithful character and actual Hall scalar spectrum give
V₁=[V₁,D₀] and V₁≤V_H. Action/SourceComplete applies these results and
discharges their local intermediate premises.
Source: Aschbacher--Smith, 11.3.7, printed p.773.
-/
