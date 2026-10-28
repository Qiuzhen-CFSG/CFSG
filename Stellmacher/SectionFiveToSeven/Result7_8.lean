module

public import Stellmacher.SectionFiveToSeven.Defs

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u v

-- This source-facing declaration retains its baseline placeholder while its proof is completed.
set_option warningAsError false in
/-- **Stellmacher (7.8).**  The local dihedral-product configuration forced
by a subgroup of `Q_l` whose Frattini subgroup lies in `Q_d`.

The source's `Z_l^L` is an orbit of subgroups: its proof says that `O₂(L)`
normalizes every member of that orbit.  Accordingly the interchange clause
quantifies conjugate subgroups, not arbitrary elements in their union. -/
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
      (∀ Z1 Z2 : Subgroup G,
        Z1 ∈ conjugateSubgroupOrbit (z Γ l) L →
        Z2 ∈ conjugateSubgroupOrbit (z Γ l) L →
        ∃ t : L, _root_.IsInvolution (t : G) ∧
          Z1.conjBy (t : G) = Z2 ∧ Z2.conjBy (t : G) = Z1) ∧
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
