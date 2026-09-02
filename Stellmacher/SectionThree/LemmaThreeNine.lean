module

public import Stellmacher.SectionThree.LemmaThreeEight

namespace Stellmacher.SectionThree

universe u

/-! **Stellmacher (3.9).**  The two possible orders of the triple
commutator in (a) are written explicitly. -/
public theorem lemma_three_nine
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P₁ P₂ H N : Subgroup G)
    (hP₁ : P₁ ∈ PSet (⊤ : Subgroup G) S)
    (hP₂ : P₂ ∈ PSet (⊤ : Subgroup G) S)
    (hH : H = P₁ ⊔ P₂)
    (hN : N ≤ H ∧ (N.subgroupOf H).Normal ∧
      ¬ twoResidualAmbient P₁ ≤ N ∧
      ¬ twoResidualAmbient P₂ ≤ N ∧
      ∀ N' : Subgroup G, N ≤ N' → N' ≤ H →
        (N'.subgroupOf H).Normal →
        (¬ twoResidualAmbient P₁ ≤ N' ∧
          ¬ twoResidualAmbient P₂ ≤ N') → N' = N)
    (hsolv₁ : Group.IsSolvable P₁)
    (hsolv₂ : Group.IsSolvable P₂)
    (T : Sylow 2 H)
    (hST : S ≤ sylowAmbient T)
    (Q : Subgroup G) (hQ : Q = S ⊓ twoCoreAmbient H)
    (hsolv : Group.IsSolvable H)
    (hOmega : omegaOneCenterAmbient S ≤ Q)
    (hJ : elementaryAbelianMaxJ S =
      elementaryAbelianMaxJ (sylowAmbient T)) :
    (⁅⁅omegaOneCenterAmbient S, twoResidualAmbient P₁⁆,
          twoResidualAmbient P₂⁆ = ⊥ ∧
      ⁅⁅omegaOneCenterAmbient S, twoResidualAmbient P₂⁆,
          twoResidualAmbient P₁⁆ = ⊥) ∨
    (S ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) ≤
        twoCoreAmbient P₁ ∨
      S ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) ≤
        twoCoreAmbient P₂) ∨
    ⁅omegaOneCenterAmbient S, twoResidualAmbient P₁⁆ =
      ⁅omegaOneCenterAmbient S, twoResidualAmbient P₂⁆ := by
  sorry

end Stellmacher.SectionThree
