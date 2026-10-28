module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Construction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.ModuleAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.PrimeCoreAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.SourceApplication

/-!
# The offender/action bridge for the odd reduction in 13.8.13

The actual source centralizer identity yields a faithful binary action of
H/O₂(H) on U_H/V₁. The supplied OddConstruction gives generation by P and
L₁T. With the actual critical pair and the h ∈ H from 13.8.8(2), the
parabolic-core argument makes Uγ* faithful on P*. Every nontrivial
two-subgroup of P*Uγ* consequently moves its local p-core. Restricting the
source module to that group preserves the quadratic action ratio of Uγ*.

`exists_minimal_moving_endpoint` uses the genuine D.2.1 Q, q-hat and
inclusion-minimal Q-hat-star definitions: restrict Uγ* to P*Uγ*, select a
cubic actor attaining the global minimum there, and prove that it moves
the local odd core. `prime_restriction_on_Utilde` applies the universal
D.2.13(1) implication and concludes p=3 or p=5. All its local action,
finite-minimum and movement hypotheses are discharged. The universal
D.2.13 implication remains an explicit earlier-source input, owned by
the D.2 development.

The local assembly still has to instantiate the standing setup and the
complete earlier-source conclusions, including the genuine 13.8.8(2)
Q-membership. `SourceApplication` accepts the literal `QuadraticMember`
output of the critical geometry and derives faithfulness from the source
centralizer identity. These modules prove the conditional prime restriction,
not all of 13.8.13 or the final ReducedOdd existence theorem. No Frattini
irreducibility premise is needed for this step.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.8(2)
and 13.8.13, printed pp.949–951; D.2.1 and D.2.13, pp.178 and 184–185.
-/
