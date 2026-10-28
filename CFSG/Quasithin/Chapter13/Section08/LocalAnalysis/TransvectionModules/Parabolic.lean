module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.CoreBounds
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.OrbitModels
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.QuotientTransport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Assembly

/-!
# Parabolic calculations for 13.8.6

The original source module hypotheses now construct the weight-four marking,
the actual S₃ quotient of K₂T, the A₆ quotient of L, both commutator core
bounds and U₂=[U₂,L₂]≤U_L. The source marking transports the literal
three-space orbit to the computed model orbit of dimension two or three.
The local residual, generation and commutator premises of the doubling
argument are all derived, and its dimensions are converted to group ranks.
The compatible S₃ coordinates on I₂/O₂(I₂) and V/V₂ are constructed from
the natural setup. `SourceAssembly.source_parabolic_conclusions` combines
these results without any remaining local marking or rank premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.6,
printed p.948. The exact universal earlier 13.7.6(3) and 13.5.4 implications
remain permitted inputs. This establishes clauses (1), (2), (3), (6) and
the ranks in (4), (5); the remaining module assertions belong to Quotients.
-/
