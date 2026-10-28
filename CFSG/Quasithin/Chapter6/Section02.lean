module

public import Theory.GroupTheory.SubgroupConjugateIncidence
public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.MarkedIntersection

/-!
# Identifying M₂₂ via L₂(4) on its natural module

The elementary incidence argument used in 6.2.5(4),(6) is available through
`Subgroup.conjugate_eq_of_subgroup_fusion` and
`Subgroup.conjugate_eq_of_unique_incidence`. Fusion inside `V` and control of
the distinguished four-subgroup's normalizer imply uniqueness of a containing
conjugate; the hyperplane conclusion then follows from the module orbit.

The natural Sylow plane now supplies its exact order and commutator identity.
The literal marked-quotient consumer constructs the normal elementary sixteen
and symmetric-four quotient in the involution centralizer. Normalization in
Hypothesis 6.1.1 replaces a separate block premise, and its compatible
symmetric-five quotient proves the layer/core equality. The actual cubic conjugate
cores now meet in exactly Z_S, discharging that marked-intersection premise. The natural reduction,
that quotient marking and the extraspecial orbit geometry remain explicit.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, §6.2, printed pp. 679–692. The local hypotheses of
these helpers still need to be established from Hypothesis 6.1.1. The terminal
identification 6.2.19 and reduction 6.2.20 are not asserted here yet.
-/
