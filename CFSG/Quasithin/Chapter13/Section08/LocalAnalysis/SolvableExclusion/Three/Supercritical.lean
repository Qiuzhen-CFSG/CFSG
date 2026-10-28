module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Movement
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Construction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Frattini
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Assembly
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.SourceApplication

/-!
# Supercritical reduction in 13.8.13

`exists_reducedOdd` constructs an actual odd subgroup P ≤ H with small normal
star image, nontrivial Vα* action, P outside M, minimal generation and an
irreducible Frattini action, and restricts its prime to three or five.
A.1.21 and A.1.24 are discharged by their proved source theorems. The precise
universal D.2.13(1) implication and 13.8.12 residual alternative remain explicit.

`exists_selected_reducedOdd` constructs the faithful action on U_H/V₁ and
the selected critical-pair offender from the complete earlier geometric
inputs. Its D.2.13 application selects a minimal cubic offender in P*Uγ*
and proves that it moves the local odd core. The subsequent three-primary
exclusions and full solvable-overgroup theorem remain separate consumers.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the first
paragraph of the proof of 13.8.13, printed pp.950–951.
-/
