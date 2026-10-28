module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.LocalStructure

/-!+# Extraspecial-order-32 recognition: the source boundary and local structure

Aschbacher–Smith I.4.6, printed p.417, has three global alternatives: a normal
elementary eight with quotient `PSL₃(2)`; `A₈` or `A₉` with neither quaternion
subgroup normal in the involution centralizer; or `M₁₂` with both normal.
`Extraspecial32.Hypotheses` and `Extraspecial32.Conclusion` retain exactly
these hypotheses and alternatives, using the intrinsic generalized Fitting
subgroup and concrete groups.

The local results prove the quaternion–quaternion structure from the source
fixed-point hypothesis, the existence of exactly two quaternion subgroups,
and their exhaustive, exclusive normality dichotomy in the centralizer.
They also supply the core, centralizer, and Sylow orders, the distinguished
center line, and the core's ambient normalizer.

The two global recognition branches remain open. This module does not yet
assert I.4.6. Final assembly must identify the ambient group, or construct
the normal elementary eight and its actual projective quotient, in each
normality branch. Neither a local factorization nor a branch hypothesis is
a substitute for that global recognition argument.
-/
