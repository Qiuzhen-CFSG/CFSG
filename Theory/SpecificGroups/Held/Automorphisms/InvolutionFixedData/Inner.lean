module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Reduction
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoB

/-!
# Assembly of the inner Held involution rows

Conjugacy coverage reduces the two inner rows of GLS3 Table 5.3p to the
literal representatives `Held.a` and `max5First ^ 4`. Centerlessness
identifies element order with inner-automorphism order. Restricting each
conjugation to fixed subgroups transports normality, quasisimplicity,
index, center order, and the actual central-quotient isomorphism.

The final theorems discharge the representative calculations and exhaustive
coverage using their checked proofs. They establish both `InnerRows` and
`InnerRowsWithQuotient` on the actual degree-2058 carrier, without extra
premises. The original conditional assembly results remain available.
Source: GLS3 Table 5.3p and its interpretation on printed pp.260–261;
Aschbacher–Smith, E.6.23 (printed p.254).
-/

public section

namespace Held.InvolutionFixedData

/-- The two representatives and exhaustive conjugacy coverage imply the full,
quotient-sensitive row statement. The three finite calculations remain explicit. -/
theorem innerRowsWithQuotient_of_representatives
    (hcoverage : InnerInvolutionCoverage)
    (hA : HasPSL3FourNormalOfIndexTwo (MulAut.conj a).fixedSubgroup)
    (hB : Nat.card (MulAut.conj (TwoLocalCandidates.max5First ^ 4)).fixedSubgroup = 21504) :
    InnerRowsWithQuotient := by
  intro g hg
  have hg' : orderOf g = 2 := (orderOf_conj g).symm.trans hg
  rcases hcoverage g hg' with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact Or.inl (hA.of_mulEquiv (innerFixedEquiv (MulAut.conj c) a))
  · exact Or.inr ((Nat.card_congr
      (innerFixedEquiv (MulAut.conj c) (TwoLocalCandidates.max5First ^ 4)).toEquiv).symm.trans hB)

/-- The same three calculations also establish the original A₆-facing contract. -/
theorem innerRows_of_representatives
    (hcoverage : InnerInvolutionCoverage)
    (hA : HasPSL3FourNormalOfIndexTwo (MulAut.conj a).fixedSubgroup)
    (hB : Nat.card (MulAut.conj (TwoLocalCandidates.max5First ^ 4)).fixedSubgroup = 21504) :
    InnerRows :=
  (innerRowsWithQuotient_of_representatives hcoverage hA hB).forget

/-- Every inner involution has the genuine 2A normal quasisimple cover, with
its actual central quotient isomorphic to matrix PSL₃(4), or a fixed subgroup
of order 21504. Coverage and both representative rows are proved. -/
theorem innerRowsWithQuotient : InnerRowsWithQuotient :=
  innerRowsWithQuotient_of_representatives Coverage.innerInvolutionCoverage
    TwoA.hasPSL3FourNormalOfIndexTwo twoB_fixedSubgroup_card

/-- The original A₆-facing inner-row contract, retaining the same normal
quasisimple subgroup of index two and center order four in the 2A case. -/
theorem innerRows : InnerRows :=
  innerRowsWithQuotient.forget

end Held.InvolutionFixedData
