module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.Quotients
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.Frattini
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.Structure
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.QuotientActions

/-!
# Intrinsic even Clifford group on six letters

The coordinate group of order 64 is intrinsically the marked central product
`C₄ * Q₈ * Q₈`. The four specified adjacent-pair monomials generate its two
commuting quaternion factors; their common sign involution is the Frattini
subgroup, and the volume generates its cyclic-four center.

The signed permutation formula supplies an A₆ action fixing the center and
generating the group by its displacements. The original coordinate projections
identify the sign/Frattini quotient with the even permutation module and the
full-center quotient with the natural deleted section, intertwining the actual
quotient actions. All action equations allow an explicit actor automorphism.

This is the intrinsic model interface for Aschbacher–Smith I.2.2(6), combined
manuscript of 1 March 2004, printed pp.410 and 412. Recognition of an actual
covering radical and comparison of its action with this model are separate.
-/
