module
public import Comparator.BenderSuzukiTheorem.Defs

universe u

namespace BSTheorem

/-- **The Bender-Suzuki theorem.** -/
public theorem bender_suzuki {X : Type u} [Group X] [Finite X] [IsSimpleGroup X] (M : Subgroup X)
    (hM : IsStronglyEmbedded M) : IsSimpleBenderGroup X := by
  sorry

end BSTheorem
