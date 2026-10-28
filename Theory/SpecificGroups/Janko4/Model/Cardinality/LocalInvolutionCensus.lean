module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Base
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Coordinates
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Representatives
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Reduction
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Counting
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Assembly

/-!
# The certified local max2 involution census

`Base` fixes the actual local subgroup, its embedding, and the three ambient
conjugacy conditions needed for Thompson counting. `Coordinates` proves that,
under the local order upper bound, every fiber of the certified row quotient
has the prescribed 8192 kernel-word representatives.

`Representatives` fixes the concrete words for the finite certificates.
`Reduction` lifts quotient coverage and finite fiber coverage to conjugacy
inside the literal local subgroup. `Counting` bounds a local class by its
quotient class size times the size of one fiber, so upper bounds suffice.

`Assembly` combines the proved quotient, fiber and ambient-fusion certificates.
It bounds the A,A set by 112266 and the B,A set by 81840, and covers the B,B set
by three H-conjugacy classes with respective bounds 2772, 221760 and 532224.
Only `Nat.card H ≤ 21799895040` remains a premise: the two literal ambient
representatives are proved nonconjugate using their distinct displacement ranks.
Full-centralizer transport and the ambient order calculation remain separate.

Source motivation: Aschbacher--Smith, `refs/quasithin.pdf`, printed pp.64--65,
A.6.1--4. ATLAS word attribution is retained in `TwoCoreCentralizer/source/`.
-/
