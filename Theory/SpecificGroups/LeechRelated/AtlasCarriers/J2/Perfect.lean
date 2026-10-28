module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Theory.GroupTheory.PerfectTriangle

/-!
# Perfectness of the actual Hall--Janko permutation carrier

The two published generators satisfy the checked (2,3,7) triangle relations.
Their images in every abelian quotient are trivial, since 2 and 3 are
coprime and their product is coprime to 7. Since they generate the entire
degree-100 carrier, that carrier is perfect.

The argument uses the literal ATLAS permutations and the kernel-checked
relations in `GeneratorPair`. It needs neither simplicity nor a comparison
with the icosian group. Source data and its attribution are retained in
`J2/source/`. The representation consumer in `G2FourModule.ConstituentDescent`
uses this certificate to prove determinant one.
-/

public section
namespace Sporadic.LeechRelated.J2

/-- Perfectness follows from the checked generators, with no inherited
simplicity hypothesis. -/
theorem carrier_isPerfect : Group.IsPerfect Carrier := by
  have h := Group.isPerfect_closure_pair_of_coprime_triangle
    GeneratorPair.a GeneratorPair.b (by decide : Nat.Coprime 2 3)
    (by decide : Nat.Coprime (2 * 3) 7)
    GeneratorPair.a_pow_two GeneratorPair.b_pow_three GeneratorPair.ab_pow_seven
  rw [GeneratorPair.closure_pair_eq_top] at h
  exact Group.IsPerfect.top_iff.mp h

end Sporadic.LeechRelated.J2
