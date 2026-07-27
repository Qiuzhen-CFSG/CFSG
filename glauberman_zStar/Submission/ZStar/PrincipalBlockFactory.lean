import Submission.ZStar.BlockOrthogonality
import Submission.ZStar.CharacterwiseSupport
import Submission.ZStar.LocalBlockSection

/-!
# Factory adapter for the principal two-block package

The ordinary congruence block is already constructed for every finite group.
This file packages the last two modular consequences into the uniform
existence statement consumed by `CoreFreeAssembly`.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar

namespace PrincipalBlockFactory

open PrincipalBlockConstruction

universe u

/-- Once section invariance and weak block orthogonality have been proved for
every constructed principal congruence block, the narrow block package needed
by the Z*-argument exists for every finite group. -/
theorem exists_principalTwoBlockData_of_congruence_inputs
    {G : Type u} [Group G] [Finite G]
    (section_invariance :
      ∀ d : PrincipalCongruenceBlockData G,
        ∀ i ∈ d.block, ∀ z : G, IsInvolution z → ∀ v : G,
          v ∈ (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
            (Subgroup.centralizer ({z} : Set G)).subtype →
          d.chi i (ConjClasses.mk (z * v)) =
            d.chi i (ConjClasses.mk z))
    (orthogonal_one :
      ∀ d : PrincipalCongruenceBlockData G,
        ∀ s : G, IsInvolution s →
          ∑ i ∈ d.block,
            d.chi i (ConjClasses.mk s) *
              d.chi i (ConjClasses.mk (1 : G)) = 0) :
    Nonempty (PrincipalTwoBlockData G) := by
  rcases exists_principalCongruenceBlockData G with ⟨d⟩
  exact ⟨d.toPrincipalTwoBlockData
    (section_invariance d) (orthogonal_one d)⟩

/-- Uniform form of the factory adapter, matching the strong-induction
assembly's hypothesis exactly. -/
theorem principalTwoBlockData_factory_of_congruence_inputs
    (section_invariance :
      ∀ (G : Type u) [Group G] [Finite G],
        ∀ d : PrincipalCongruenceBlockData G,
          ∀ i ∈ d.block, ∀ z : G, IsInvolution z → ∀ v : G,
            v ∈ (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
              (Subgroup.centralizer ({z} : Set G)).subtype →
            d.chi i (ConjClasses.mk (z * v)) =
              d.chi i (ConjClasses.mk z))
    (orthogonal_one :
      ∀ (G : Type u) [Group G] [Finite G],
        ∀ d : PrincipalCongruenceBlockData G,
          ∀ s : G, IsInvolution s →
            ∑ i ∈ d.block,
              d.chi i (ConjClasses.mk s) *
                d.chi i (ConjClasses.mk (1 : G)) = 0) :
    ∀ (G : Type u) [Group G] [Finite G],
      Nonempty (PrincipalTwoBlockData G) := by
  intro G _ _
  exact exists_principalTwoBlockData_of_congruence_inputs
    (section_invariance G) (orthogonal_one G)

/-- The completed weak-orthogonality theorem reduces the uniform block-data
factory to the single remaining local support statement.  This adapter does
not assume section invariance itself: it derives it from the canonical local
principal-block core support theorem. -/
theorem principalTwoBlockData_factory_of_canonicalLocalCoreSupport
    (local_support :
      ∀ (G : Type u) [Group G] [Finite G],
        ∀ d : PrincipalCongruenceBlockData G,
          ∀ i ∈ d.block, ∀ z : G, IsInvolution z →
            LocalBlockSection.CanonicalLocalPrincipalBlockCoreSupport d i z) :
    ∀ (G : Type u) [Group G] [Finite G],
      Nonempty (PrincipalTwoBlockData G) := by
  apply principalTwoBlockData_factory_of_congruence_inputs
  · intro G _ _ d
    exact
      LocalBlockSection.principalBlock_section_invariance_of_canonicalLocalPrincipalBlockCoreSupport
        d (local_support G d)
  · intro G _ _ d
    exact BlockOrthogonality.weak_block_orthogonality d

/-- Unconditional uniform factory for the principal-`2`-block package used by
the Z*-assembly. -/
theorem principalTwoBlockData_factory :
    ∀ (G : Type u) [Group G] [Finite G],
      Nonempty (PrincipalTwoBlockData G) := by
  apply principalTwoBlockData_factory_of_canonicalLocalCoreSupport
  intro G _ _ d i hi z hzI
  exact CharacterwiseSupport.canonicalLocalPrincipalBlockCoreSupport
    d i hi z hzI

end PrincipalBlockFactory

end Submission.ZStar
