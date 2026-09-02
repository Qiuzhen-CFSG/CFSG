module

public import Stellmacher.SectionFiveToSeven.Defs

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (5.2).**  The subnormality conclusion for a subgroup `K`
of a member of `𝒫*(C,S₀)`. -/
public theorem lemma_five_two
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H)
    (Z0 B0 C P K : Subgroup H)
    (hZ0 : Z0 = omegaOneCenter (S0 : Subgroup H))
    (hB0 : B0 = baumannIn (S0 : Subgroup H))
    (hC : C = Subgroup.centralizer (Z0 : Set H))
    (hP : P ∈ PStarFamily C (S0 : Subgroup H))
    (hK : K ≤ P)
    (hlocal : ∀ U : Subgroup H,
      Theory.Quasithin.IsTwoLocal U → B0 ≤ U →
        Group.IsSolvable U ∧ Stellmacher.IsCharacteristicTwoType U)
    (hcomm : K = ⁅K, B0⁆) :
    ∀ U : Subgroup H, Theory.Quasithin.IsTwoLocal U →
      B0 ⊔ K ≤ U → SubnormalIn K U := by
  sorry

end Stellmacher.SectionsFiveToSeven
