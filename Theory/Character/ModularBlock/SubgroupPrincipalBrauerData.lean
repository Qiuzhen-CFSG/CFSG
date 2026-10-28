module
public import Theory.Character.ModularBlock.SubgroupBrauerMap
public import Theory.Character.ModularBlock.CompatibleBrauerBlock
/-!
# Direct subgroup restriction of the principal selector

The subgroup Brauer restriction of the reduced principal selector is central
and, for a two-subgroup, is an idempotent with augmentation one. Define its
extra term by subtracting the compatible local principal selector. This
difference is central, reconstructs the original restriction by addition,
and has augmentation zero.

The restriction results use the proved subgroup Brauer map and the reduced
selector's centrality, idempotence, and augmentation. The extra-term results
use the exact compatible residue-field inclusion and ring identities.
No assertion that the extra term is an idempotent is made here; that step
uses the local selector's principal primitivity in the final comparison.

Ported from the independent data clauses of revision c3503435,
public/lean-eval/glauberman_zStar,
Submission/ZStar/SubgroupPrincipalBrauer.lean. The extra-term definition
exposes its coefficient expression for downstream factor comparisons.
-/

public section
noncomputable section
namespace ModularBlock.SubgroupPrincipalBrauer
open PrincipalBlockConstruction
universe u
attribute [local instance] Fintype.ofFinite
/-- The direct subgroup Brauer image of the reduced ambient principal-block
idempotent is central. -/
theorem reducedPrincipalBlockElement_subgroupRestriction_mem_center
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) :
    DefectSupport.subgroupCentralizerRestriction
        (BrauerBlockReduction.principalResidueField d) Q
        (BrauerBlockReduction.reducedPrincipalBlockElement d) ∈
      Set.center
        (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer (Q : Set G))) := by
  exact SubgroupBrauerMap.subgroupCentralizerRestriction_mem_center
    Q (BrauerBlockReduction.reducedPrincipalBlockElement d)
    (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d)

/-- The direct subgroup Brauer image of the reduced ambient principal-block
idempotent is idempotent. -/
theorem reducedPrincipalBlockElement_subgroupRestriction_isIdempotent
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    IsIdempotentElem
      (DefectSupport.subgroupCentralizerRestriction
        (BrauerBlockReduction.principalResidueField d) Q
        (BrauerBlockReduction.reducedPrincipalBlockElement d)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact
    SubgroupBrauerMap.subgroupCentralizerRestriction_isIdempotent_of_mem_center
      Q hQ (BrauerBlockReduction.reducedPrincipalBlockElement d)
      (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d)
      (BrauerBlockReduction.reducedPrincipalBlockElement_isIdempotent d)

/-- Subgroup Brauer restriction preserves the augmentation-one property of
the ambient principal selector. -/
theorem reducedPrincipalBlockElement_subgroupRestriction_augmentation_eq_one
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G))
        (DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d)) = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [SubgroupBrauerMap.augmentation_subgroupCentralizerRestriction
      Q hQ (BrauerBlockReduction.reducedPrincipalBlockElement d)
      (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d),
    BrauerBlockReduction.reducedPrincipalBlockElement_augmentation_eq_one]

/-- The complementary part of the direct `Q`-Brauer image after removing
the compatible principal block of `C_G(Q)`. -/
@[expose] noncomputable def extraBrauerFactor
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) :
    MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)) :=
  DefectSupport.subgroupCentralizerRestriction
      (BrauerBlockReduction.principalResidueField d) Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d) -
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer (Q : Set G))

theorem extraBrauerFactor_mem_center
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) :
    extraBrauerFactor d Q ∈
      Set.center
        (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer (Q : Set G))) := by
  apply (Semigroup.mem_center_iff).2
  intro a
  rw [extraBrauerFactor, mul_sub, sub_mul,
    Semigroup.mem_center_iff.mp
      (reducedPrincipalBlockElement_subgroupRestriction_mem_center d Q) a,
    Semigroup.mem_center_iff.mp
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_mem_center
        d (Subgroup.centralizer (Q : Set G))) a]

/-- The direct subgroup Brauer image splits as its principal factor plus the
complementary factor. -/
theorem subgroupRestriction_eq_local_add_extra
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) :
    DefectSupport.subgroupCentralizerRestriction
        (BrauerBlockReduction.principalResidueField d) Q
        (BrauerBlockReduction.reducedPrincipalBlockElement d) =
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer (Q : Set G)) +
        extraBrauerFactor d Q := by
  simp [extraBrauerFactor]

/-- The complementary direct Brauer factor has augmentation zero. -/
theorem extraBrauerFactor_augmentation_eq_zero
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G))
        (extraBrauerFactor d Q) = 0 := by
  rw [extraBrauerFactor, map_sub,
    reducedPrincipalBlockElement_subgroupRestriction_augmentation_eq_one d Q hQ,
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one,
    sub_self]

end ModularBlock.SubgroupPrincipalBrauer


