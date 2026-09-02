module

public import Stellmacher.SectionFiveToSeven.Defs


namespace Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (6.3).**  Under the same nontrivial-action hypothesis as
(6.2), each quotient `Pᵢ/O₂(Pᵢ)` is dihedral of order `2·3ⁿⁱ`.  The
parameter of Mathlib's `DihedralGroup` is the half-order. -/
public theorem lemma_six_three
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ ≠ ⊥) :
    (∃ n1 : ℕ,
      Nonempty ((P1 ⧸ pCore 2 P1) ≃* DihedralGroup (3 ^ n1))) ∧
    (∃ n2 : ℕ,
      Nonempty ((P2 ⧸ pCore 2 P2) ≃* DihedralGroup (3 ^ n2))) := by
  sorry

end Stellmacher.SectionsFiveToSeven
