module

public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.PSL3Three.EvenLocals

/-!
# Even characteristic of PSL₃(3)

The intrinsic SL₃(3) calculation identifies every maximal two-local containing
any Sylow two-subgroup with an involution centralizer. Each such centralizer
is GL₂(3) and has self-centralizing two-core. The canonical projection
SL₃(3) ≃ PSL₃(3) transports condition E to the actual projective model.

This proves the even-characteristic clause for PSL₃(3) in Aschbacher–Smith,
Theorem 0.1.2(4), printed p.4, repeated as Theorem 0.1.1(4) on p.482.
-/

namespace CFSG.Quasithin.MainConverse

/-- The concrete projective group PSL₃(3) satisfies condition E for every Sylow two-subgroup. -/
public theorem psl3_three_evenCharacteristic :
    IsEvenCharacteristic Matrix.PSL3Three.PSL := by
  apply IsEvenCharacteristic.of_equiv Matrix.PSL3Three.equiv
  intro T M hM hTM
  obtain ⟨z, hz, rfl⟩ :=
    Matrix.PSL3Three.maximalTwoLocal_eq_involutionCentralizer_SL T hM hTM
  exact Matrix.PSL3Three.involutionCentralizer_twoCore_selfCentralizing_SL z hz

end CFSG.Quasithin.MainConverse
