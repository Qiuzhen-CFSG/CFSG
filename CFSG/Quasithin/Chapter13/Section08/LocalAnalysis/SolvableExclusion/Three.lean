module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Selection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.PrimeReduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Movement
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.RankOne
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Assembly
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.SourceSelection

/-!+# The supercritical and three-primary steps in 13.8.13

The imported proofs find an odd core moved by Vα* in the actual quotient
of a solvable H. They also show that an odd subgroup with a moved normal
star image lies outside M by the exact 13.8.12 residual trichotomy. Minimality
in the genuine Hz family gives H = ⟨P,L₁,T⟩.

`exists_selected_five_or_noncontained` constructs the faithful literal action,
the selected critical geometry, and the small odd subgroup with its irreducible
Frattini action. It restricts the prime to 3 or 5 and eliminates the cyclic and
contained three-primary cases using the proved rank-one contradictions.

Only the noncontained elementary-nine and extraspecial-27 cases remain before
`ReducedFive`. The endpoints in `Noncontained` still require their action and
rank witnesses; they do not discharge these branches. This module therefore
does not yet assert existence of `ReducedFive` or solvable-overgroup exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed pp.950–951.
-/
