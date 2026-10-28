module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.LocalInertia
public import Theory.Character.ModularBlock.NormalizerEmbedding

/-!
# The literal local element in the normalizer algebra

Embed the Sylow Brauer image of the reduced principal projector along
`C_G(P) ↪ N_G(P)`. Normalizer invariance makes the result central;
multiplicativity of the Brauer map makes it idempotent; augmentation is one.
These statements fix the local element whose simple modules are counted in
the prime-order case of Feit VII.1.3 and VII.3.12.

They do not assert that its embedding is primitive, nor do they identify
its simple modules with the ambient ones. Those are separate local and
Green-correspondence arguments.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount
open ModularBlock ModularBlock.PrimeBlockConstruction ModularBlock.NormalizerBrauerAction

variable {K G : Type*} [Field K] [Group G] [Finite G] {p : ℕ}

/-- The actual Brauer image, embedded in the algebra of the actual normalizer. -/
@[expose] def normalizerSelector (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K) (P : Sylow p G) :
    MonoidAlgebra K (Subgroup.normalizer (P : Set G)) :=
  normalizerAlgebraEmbedding K (P : Subgroup G)
    (DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G)
      (reducedPrincipal d residue))

theorem normalizerSelector_mem_center (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K) (P : Sylow p G) :
    normalizerSelector d residue P ∈
      Set.center (MonoidAlgebra K (Subgroup.normalizer (P : Set G))) := by
  apply normalizerAlgebraEmbedding_mem_center_of_fixed
  intro x
  exact subgroupRestriction_mapDomain_centralizerConjEquiv_eq_self
    (P : Subgroup G) x _ (reducedPrincipal_mem_center d residue)

variable [Fact p.Prime] [CharP K p]

theorem normalizerSelector_isIdempotent (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K) (P : Sylow p G) :
    IsIdempotentElem (normalizerSelector d residue P) :=
  (SubgroupBrauerMap.subgroupCentralizerRestriction_isIdempotent_of_mem_center
    (P : Subgroup G) P.isPGroup' _ (reducedPrincipal_mem_center d residue)
    (reducedPrincipal_isIdempotent d residue)).map
      (normalizerAlgebraEmbedding K (P : Subgroup G))

theorem normalizerSelector_augmentation (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K) (P : Sylow p G) :
    groupAlgebraAugmentation K (Subgroup.normalizer (P : Set G))
      (normalizerSelector d residue P) = 1 := by
  exact (augmentation_normalizerAlgebraEmbedding (R := K) (P : Subgroup G) _).trans
    ((SubgroupBrauerMap.augmentation_subgroupCentralizerRestriction
      (P : Subgroup G) P.isPGroup' _ (reducedPrincipal_mem_center d residue)).trans
        (reducedPrincipal_augmentation d residue))

theorem normalizerSelector_ne_zero (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K) (P : Sylow p G) :
    normalizerSelector d residue P ≠ 0 := by
  intro hz
  have h := normalizerSelector_augmentation d residue P
  rw [hz, map_zero] at h
  exact zero_ne_one h

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount
