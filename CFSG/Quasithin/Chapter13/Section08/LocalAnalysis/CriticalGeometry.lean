module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Transvections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.QuotientActions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankOne
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.LocalConsequences
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.ComponentCommutator
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.CommutatorComparison
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankBounds
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Endpoint

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.PreliminaryGeometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.FinalAssembly

/-!
# Critical-pair geometry and quotient actions in §13.8

The imported proofs establish the geometric clauses of 13.8.4, the complete
symmetry argument of 13.8.7 (including the five-dimensional-cover contradiction),
the corrected alternatives of 13.8.8, both clauses of 13.8.9 and corrected
13.8.10, both rank deductions of 13.8.11, and all four clauses of 13.8.18.
They preserve the actual cosets, critical distance, geodesic, terminal edge,
conjugators, subgroup quotients and quotient actions.

`PreliminaryGeometry` proves parity, core containment, abelianness for b>3,
the length-three line containment, and the quadratic quotient actions.
`LocalConsequences` supplies the flag intersection and strict spans.
`Reorientation.strict_iff` constructs the reverse pair before using the
proved asymmetric impossibility. `FinalAssembly` discharges the quadratic
and terminal-edge inputs, proves the last rank bound, and constructs a
selected pair retaining the offender, edge-core placement and every-F
generation on that same pair. Component generation uses the proved full
commutator calculation, with normality relative to the endpoint group.

The source corrections are recorded rather than hidden: 13.8.10 requires
D_H<U_H, and `alternatives_from_earlier_inputs` uses the proof-supported
vertex and actors of `Reorientation.alternatives_corrected`. The printed
δ=g_b⁻¹γ equals γ₁ and is distinct from the required g_b⁻¹γ₁.

This is the conditional geometry contract. The parent supplies the genuine
standing setup, the precise earlier 13.2/13.3/13.5/13.7/F.9 inputs, the
permutation clause of 13.8.4(5), the earlier 13.8.5–6 model conclusions,
and the component hypotheses explicitly enumerated in the descendants.
These are not an unconditional proof of the complete §13.8 counterexample
argument. No remaining geometric or quotient-action premise is delegated
back as the conclusion of its own theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.947–950 and 953 (PDF pp.964–967 and 970).
-/
