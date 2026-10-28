module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.ResidualTransport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.Quotient
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.Assembly

/-!
# Source marking and earlier applicability for 13.8.6

`Marking.source_marking_and_core` constructs the source marking and proves
its earlier-theorem applicability in both the natural and augmentation-cover
cases. It uses the literal section U_H/V₁ and the original natural action
on V. The natural section of [U_H,K], the A₆ quotient of L, full faithful
H* coordinates, compatible point/plane flags, A₄ residual image and
surjections onto the actual duad parabolics are all connected. Their kernels
are two-groups, giving the literal S₃ quotient of K₂T by its two-core.

The original natural L-action and flag discharge the applicability of
13.5.4 and give all residual and generation identities consumed by
`source_core_bounds_and_generation`. The assembly yields both core bounds
and U₂=[U₂,L₂]≤U_L. The two relative-normalizer definitions of Lᵢ agree.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.7.6(3), printed pp.938–939, 13.5.4, p.916, and 13.8.6, p.948.
This is a conditional prerequisite with the exact earlier universal
13.7.6(3) and 13.5.4 implications explicit. The full source 13.8.6 assembly,
including the rank and representation clauses (4),(5), belongs to the parent.
-/
