module

public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.Reduction
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.Quartic
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.StandardBound
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.GraphFieldSelection

/-!
# Outer elementary actors of binary PSL₃

An elementary two-subgroup of Aut(PSL₃(2ᶠ)) not contained in the inner
automorphisms has generator rank at most f+1. Standard automorphism coverage
and the outer-image bound reduce the proof to the literal fixed groups of
outer involutions. An outer image of rank at most one uses fixed rank at
most f; an outer image of rank two contains a graph-field actor, whose
whole fixed group has rank at most f-1. The binary case is handled by the
proved Aut(PSL₃(2)) calculation, and the unitary estimate includes the
whole quartic fixed group.

All model calculations and actor selection are discharged here. The
conditional reductions and the separate quartic calculation remain exported.

Source: Aschbacher–Smith E.1.14(1), printed p.214; GLS3, Theorem 2.5.12
and §2.7. The declarations retain the actual automorphisms and inner subgroup.
-/

public section
open scoped MatrixGroups
namespace Matrix.PSL3Even.OuterElementaryRank
variable {F : Type*} [Field F] [Finite F]

/-- The sharp bound for elementary outer actors on the actual projective
linear group, including f=1 and with no model-calculation premises. -/
theorem rank_le_of_not_le_inner {f : ℕ} (hf : 0 < f)
    (hF : Nat.card F = 2 ^ f)
    (E : Subgroup (MulAut PSL(3,F))) (hE : IsElementaryAbelian 2 E)
    (hEO : ¬ E ≤ MulAut.innerSubgroup PSL(3,F)) : Group.rank E ≤ f + 1 :=
  rank_le_of_fixed_bounds hf hF
    (FixedRanks.outer_involution_fixed_rank_le hf hF)
    (FixedRanks.graphField_involution_fixed_rank_le hf hF) E hE hEO

end Matrix.PSL3Even.OuterElementaryRank
