module

public import Stellmacher.SectionFiveToSeven.Defs

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (6.2).**  If `P₂` acts nontrivially on
`Ω₁(Z(S))`, then `J(S)` is not contained in either local 2-core. -/
public theorem lemma_six_two
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ ≠ ⊥) :
    ¬ elementaryAbelianMaxJ (G := H) S ≤ twoCoreIn P1 ∧
      ¬ elementaryAbelianMaxJ (G := H) S ≤ twoCoreIn P2 := by
  sorry

end Stellmacher.SectionsFiveToSeven
