module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction.RankInputs
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank

/-!
# The signed-three rank witnesses for the higher-field sieve

The two linear and two unitary inequalities come from explicit cubic matrix
subgroups. The projective witnesses use a diagonal cubic and a coordinate
three-cycle, accounting for the scalar kernel; the special witnesses use
two determinant-one diagonal cubics. No rank or simplicity premise is added.

Source: Aschbacher–Smith, proof of 13.8.20(a), printed p.954 (PDF p.971).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction

/-- The four genuine cubic rank-two witnesses used in the signed-three sieve. -/
theorem signedThreeRanks : SignedThreeRanks := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F _ _ n _ hF hn
    exact Theory.SpecificGroups.SignedThreeCubicRank.linear_special hF hn
  · intro F _ _ n _ hF hn
    exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective hF hn
  · intro F _ _ J n hn hF hconj ho
    exact Theory.SpecificGroups.SignedThreeCubicRank.unitary_special J (by omega) hF hconj ho
  · intro F _ _ J n hn hF hconj ho
    exact Theory.SpecificGroups.SignedThreeCubicRank.unitary_projective J (by omega) hF hconj ho

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction
end
