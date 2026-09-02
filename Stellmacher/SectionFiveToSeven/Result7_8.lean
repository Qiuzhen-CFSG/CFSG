module

public import Stellmacher.SectionFiveToSeven.Defs

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u v

/-- **Stellmacher (7.8).**  The local dihedral-product configuration forced
by a subgroup of `Q_l` whose Frattini subgroup lies in `Q_d`. -/
public theorem lemma_seven_eight
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2)
    (d l : Γ.Vertex) (hl : l ∈ neighborhood Γ d)
    (A : Subgroup G)
    (hA : A ≤ q Γ l)
    (hAnot : ¬ A ≤ q Γ d)
    (hPhi : frattiniAmbient A ≤ q Γ d) :
    ∃ x : G, ∃ A0 L : Subgroup G,
      x ∈ stabilizer Γ d ∧
      A0 ≤ A ∧
      L = A ⊔ conjugateBy A x ∧
      Nat.card A = 2 * Nat.card A0 ∧
      x ∈ L ∧
      x ^ 2 ∈ q Γ d ∧
      A0 = A ⊓ twoCoreIn L ∧
      L ⊔ (stabilizer Γ l ⊓ stabilizer Γ d) = stabilizer Γ d ∧
      Nonempty (QuotientDihedralProduct L (q Γ d) A0) ∧
      (∀ y1 y2 : G,
        y1 ∈ conjugateOrbit (z Γ l) L →
        y2 ∈ conjugateOrbit (z Γ l) L →
        ∃ t : G, t ∈ L ∧ IsInvolution t ∧
          t * y1 * t⁻¹ = y2 ∧ t * y2 * t⁻¹ = y1) ∧
      (∀ a : G, a ∈ A → a ∉ A0 →
        L = Subgroup.closure ({a} : Set G) ⊔ conjugateBy A x) ∧
      (∀ T : Sylow 2 ↥(stabilizer Γ d ⊓ stabilizer Γ l),
        baumannIn (sylowTwoAmbient (stabilizer Γ d ⊓ stabilizer Γ l) T) ≤
            q Γ d ∨
          twoResidualIn L ≤
            ⁅twoResidualIn L,
              baumannIn (sylowTwoAmbient (stabilizer Γ d ⊓ stabilizer Γ l) T)⁆) := by
  sorry

end Stellmacher.SectionsFiveToSeven
