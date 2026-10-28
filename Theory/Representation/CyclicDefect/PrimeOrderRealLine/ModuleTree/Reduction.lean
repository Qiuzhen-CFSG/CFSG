module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.Roots
public import Theory.Character.ModularBlock.SubgroupBrauerHom
public import Theory.Character.ModularBlock.PrimitiveCentralIdempotent

/-!
# Reduction and Sylow support of the principal congruence projector

Reduce the actual localized projector at its specified cyclotomic prime.
Ordinary character orthogonality proves augmentation one. Subgroup Brauer
restriction preserves augmentation, so every p-subgroup has nonzero Brauer
image; Sylow maximality then proves maximal Brauer support.

These results do not assert primitivity. Identifying the reduced projector
and its Sylow Brauer image as primitive central idempotents is a separate
principal-block theorem. Source: Feit, Chapters III.8--9 and VII.1; the
projector is the one constructed in `PrimeSelector`.
-/

public section
open scoped BigOperators Classical
open ModularBlock ModularBlock.PrimeBlockConstruction
open ModularBlock.PrincipalBlockConstruction ModularBlock.BlockOrthogonality
open Representation.CyclicDefect.PrimeOrderRealLine
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree
variable {p : ℕ} {G : Type*} [Group G] [Finite G]
attribute [local instance] Fintype.ofFinite

/-- Orthogonality computes augmentation before modular reduction. -/
theorem localizedPrincipal_augmentation (d : PrimeCongruenceBlockData p G) :
    groupAlgebraAugmentation (Localization.AtPrime d.primeIdeal) G
      (PrimeSelector.localizedBlockElement d d.principal) = 1 := by
  apply PrimeIntegralModels.localizationToComplex_injective d.primeIdeal
  rw [map_one, groupAlgebraAugmentation_apply, map_sum]
  simp_rw [PrimeSelector.localizedBlockElement_coeff]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hsum (i : d.I) :
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, d.chi i (ConjClasses.mk g⁻¹) =
        if i = d.principal then 1 else 0 := by
    have hinv : (∑ g : G, d.chi i (ConjClasses.mk g⁻¹)) =
        ∑ g : G, d.chi i (ConjClasses.mk g) :=
      Equiv.sum_comp (Equiv.inv G) (fun g => d.chi i (ConjClasses.mk g))
    rw [hinv]
    have h := completeFamily_orthonormal d.complete i d.principal
    rw [d.principal_eq] at h
    simpa [classFunctionInner, ordinaryPrincipalCharacter, eq_comm] using h
  simp_rw [← Finset.mul_sum]
  rw [Finset.mul_sum]
  simp_rw [show ∀ i : d.I, (Nat.card G : ℂ)⁻¹ *
      (d.chi i (ConjClasses.mk 1) * ∑ g : G, d.chi i (ConjClasses.mk g⁻¹)) =
      d.chi i (ConjClasses.mk 1) *
        ((Nat.card G : ℂ)⁻¹ * ∑ g : G, d.chi i (ConjClasses.mk g⁻¹)) by
    intro i; ring, hsum]
  simp [d.principal_eq, PrimeCongruenceBlockData.SameBlock]

/-- The literal reduction of the specified principal congruence projector. -/
@[expose] def reducedPrincipal (d : PrimeCongruenceBlockData p G)
    {K : Type*} [Field K] (residue : Localization.AtPrime d.primeIdeal →+* K) :
    MonoidAlgebra K G :=
  MonoidAlgebra.mapRingHom G residue (PrimeSelector.localizedBlockElement d d.principal)

theorem reducedPrincipal_mem_center (d : PrimeCongruenceBlockData p G)
    {K : Type*} [Field K] (residue : Localization.AtPrime d.primeIdeal →+* K) :
    reducedPrincipal d residue ∈ Set.center (MonoidAlgebra K G) :=
  groupAlgebra_mapRingHom_mem_center residue _
    (PrimeSelector.localizedBlockElement_mem_center d d.principal)

theorem reducedPrincipal_isIdempotent (d : PrimeCongruenceBlockData p G)
    {K : Type*} [Field K] (residue : Localization.AtPrime d.primeIdeal →+* K) :
    IsIdempotentElem (reducedPrincipal d residue) :=
  (PrimeSelector.localizedBlockElement_isIdempotent d d.principal).map _

theorem reducedPrincipal_augmentation (d : PrimeCongruenceBlockData p G)
    {K : Type*} [Field K] (residue : Localization.AtPrime d.primeIdeal →+* K) :
    groupAlgebraAugmentation K G (reducedPrincipal d residue) = 1 := by
  rw [reducedPrincipal, groupAlgebraAugmentation_mapRingHom,
    localizedPrincipal_augmentation, map_one]

theorem reducedPrincipal_brauer_ne_zero (d : PrimeCongruenceBlockData p G)
    [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    (residue : Localization.AtPrime d.primeIdeal →+* K)
    (Q : Subgroup G) (hQ : IsPGroup p Q) :
    DefectSupport.subgroupCentralizerRestriction K Q (reducedPrincipal d residue) ≠ 0 := by
  have h := SubgroupBrauerMap.augmentation_subgroupCentralizerRestriction Q hQ
    (reducedPrincipal d residue) (reducedPrincipal_mem_center d residue)
  rw [reducedPrincipal_augmentation] at h
  intro hz
  rw [hz, map_zero] at h
  exact zero_ne_one h

/-- Nonzero subgroup Brauer restriction, with the actual p-subgroup condition. -/
@[expose] def HasBrauerSupport {K : Type*} [Field K] (p : ℕ) (e : MonoidAlgebra K G)
    (Q : Subgroup G) : Prop :=
  IsPGroup p Q ∧ DefectSupport.subgroupCentralizerRestriction K Q e ≠ 0

/-- Every Sylow subgroup is maximal for the principal selector's Brauer support.
For a primitive selector this is the usual defect-group criterion. -/
theorem sylow_maximal_brauerSupport (d : PrimeCongruenceBlockData p G)
    [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    (residue : Localization.AtPrime d.primeIdeal →+* K) (P : Sylow p G) :
    Maximal (HasBrauerSupport p (reducedPrincipal d residue)) (P : Subgroup G) := by
  refine ⟨⟨P.isPGroup', reducedPrincipal_brauer_ne_zero d residue P P.isPGroup'⟩, ?_⟩
  intro Q hQ hPQ
  exact le_of_eq (P.is_maximal' hQ.1 hPQ)

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree
