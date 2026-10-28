module
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.Contracts
public import Theory.Character.ModularBlock.NormalizerAction
public import Mathlib.GroupTheory.Index

/-!
# The local principal block and its actual inertia group

The stabilizer is defined using conjugation on the group algebra of the
centralizer and is then mapped into the ambient group. The subgroup Brauer
image of a central element is fixed by the entire normalizer. If this image
is primitive, augmentation one identifies it uniquely as the local principal
block. Thus its inertia group really is the Sylow normalizer.

`PrimeOrderInput` collects the local group, primitivity and root-order inputs
for the cyclic theorem. It contains no simple count or decomposition-matrix
conclusion. The multiplicity quotient is computed here; the interpretation
as a number of exceptional characters still requires Feit VII.2.11.

Source: Feit, *The Representation Theory of Finite Groups*, VII.1, especially
VII.1.3(ii), and VII.2.11. Normalizer conjugation and Brauer invariance reuse
`Theory.Character.ModularBlock.NormalizerAction`.
-/

public section
noncomputable section
open scoped Classical
namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
open ModularBlock ModularBlock.PrimeBlockConstruction ModularBlock.NormalizerBrauerAction
variable {G : Type*} [Group G] {K : Type*} [Field K]

/-- Stabilizer of the literal local group-algebra element under normalizer conjugation. -/
@[expose] def localBlockStabilizer (Q : Subgroup G)
    (b : MonoidAlgebra K (Subgroup.centralizer (Q : Set G))) :
    Subgroup (Subgroup.normalizer (Q : Set G)) where
  carrier := {n | normalizerConjugate K Q n b = b}
  one_mem' := normalizerConjugate_one Q b
  mul_mem' := by
    intro n m hn hm
    change normalizerConjugate K Q (n * m) b = b
    rw [normalizerConjugate_mul, hm, hn]
  inv_mem' := by
    intro n hn
    have h := normalizerConjugate_inv_apply Q n b
    rw [hn] at h
    exact h

/-- The stabilizer embedded in the ambient group, as in Feit’s inertia group. -/
@[expose] def localBlockInertia (Q : Subgroup G)
    (b : MonoidAlgebra K (Subgroup.centralizer (Q : Set G))) : Subgroup G :=
  (localBlockStabilizer Q b).map (Subgroup.normalizer (Q : Set G)).subtype

/-- The index of the centralizer in the actual inertia group. -/
@[expose] def localInertialIndex (Q : Subgroup G)
    (b : MonoidAlgebra K (Subgroup.centralizer (Q : Set G))) : ℕ :=
  (Subgroup.centralizer (Q : Set G)).relIndex (localBlockInertia Q b)

theorem localBlockStabilizer_restriction (Q : Subgroup G)
    (e : MonoidAlgebra K G) (he : e ∈ Set.center (MonoidAlgebra K G)) :
    localBlockStabilizer Q (DefectSupport.subgroupCentralizerRestriction K Q e) = ⊤ := by
  apply top_unique
  intro n _
  exact subgroupRestriction_mapDomain_centralizerConjEquiv_eq_self Q n e he

theorem localBlockInertia_restriction (Q : Subgroup G)
    (e : MonoidAlgebra K G) (he : e ∈ Set.center (MonoidAlgebra K G)) :
    localBlockInertia Q (DefectSupport.subgroupCentralizerRestriction K Q e) =
      Subgroup.normalizer (Q : Set G) := by
  rw [localBlockInertia, localBlockStabilizer_restriction Q e he]
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem localInertialIndex_restriction (Q : Subgroup G)
    (e : MonoidAlgebra K G) (he : e ∈ Set.center (MonoidAlgebra K G)) :
    localInertialIndex Q (DefectSupport.subgroupCentralizerRestriction K Q e) =
      (Subgroup.centralizer (Q : Set G)).relIndex (Subgroup.normalizer (Q : Set G)) := by
  rw [localInertialIndex, localBlockInertia_restriction Q e he]

variable {p : ℕ} [Finite G]
theorem reducedPrincipal_inertia (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K) (Q : Subgroup G) :
    localBlockInertia Q
      (DefectSupport.subgroupCentralizerRestriction K Q (reducedPrincipal d residue)) =
      Subgroup.normalizer (Q : Set G) :=
  localBlockInertia_restriction Q _ (reducedPrincipal_mem_center d residue)

theorem reducedPrincipal_inertialIndex (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K) (Q : Subgroup G) :
    localInertialIndex Q
      (DefectSupport.subgroupCentralizerRestriction K Q (reducedPrincipal d residue)) =
      (Subgroup.centralizer (Q : Set G)).relIndex (Subgroup.normalizer (Q : Set G)) :=
  localInertialIndex_restriction Q _ (reducedPrincipal_mem_center d residue)

/-- A primitive Sylow Brauer image is the local principal block, as
characterized by augmentation one. -/
theorem localPrincipal_eq_restriction [Fact p.Prime] [CharP K p]
    (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K) (P : Sylow p G)
    (hlocal : IsCentrallyPrimitive
      (DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G)
        (reducedPrincipal d residue)))
    (b : MonoidAlgebra K (Subgroup.centralizer (P : Set G)))
    (hb : IsCentrallyPrimitive b)
    (haug : groupAlgebraAugmentation K (Subgroup.centralizer (P : Set G)) b = 1) :
    b = DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G)
      (reducedPrincipal d residue) := by
  have hres : groupAlgebraAugmentation K (Subgroup.centralizer (P : Set G))
      (DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G)
        (reducedPrincipal d residue)) = 1 := by
    exact (SubgroupBrauerMap.augmentation_subgroupCentralizerRestriction
      (P : Subgroup G) P.isPGroup' _ (reducedPrincipal_mem_center d residue)).trans
      (reducedPrincipal_augmentation d residue)
  apply CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive hb hlocal
  intro hz
  have h := congrArg (groupAlgebraAugmentation K
    (Subgroup.centralizer (P : Set G))) hz
  rw [map_mul, haug, hres, one_mul, map_zero] at h
  exact one_ne_zero h

/-- The inertia group of any actual local principal block is the Sylow
normalizer, once the literal Brauer image is primitive. -/
theorem localPrincipal_inertia [Fact p.Prime] [CharP K p]
    (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K) (P : Sylow p G)
    (hlocal : IsCentrallyPrimitive
      (DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G)
        (reducedPrincipal d residue)))
    (b : MonoidAlgebra K (Subgroup.centralizer (P : Set G)))
    (hb : IsCentrallyPrimitive b)
    (haug : groupAlgebraAugmentation K (Subgroup.centralizer (P : Set G)) b = 1) :
    localBlockInertia (P : Subgroup G) b = Subgroup.normalizer (P : Set G) := by
  rw [localPrincipal_eq_restriction d residue P hlocal b hb haug]
  exact reducedPrincipal_inertia d residue (P : Subgroup G)

/-- Source inputs for a principal block with prime-order defect and full
inertial index. There is no assertion about simple counts, decomposition
numbers, or graph incidence in this record. -/
structure PrimeOrderInput (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K) (m : ℕ) (P : Sylow p G) : Prop where
  sylow_card : Nat.card P = p
  cyclic : IsCyclic P
  principal_primitive : IsCentrallyPrimitive (reducedPrincipal d residue)
  local_primitive : IsCentrallyPrimitive
    (DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G)
      (reducedPrincipal d residue))
  inertial_index : localInertialIndex (P : Subgroup G)
    (DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G)
      (reducedPrincipal d residue)) = p - 1
  ordinary_card : d.block.card = p
  regular_orders : ∀ g : G, ¬ p ∣ orderOf g → orderOf g ∣ m

/-- The local expression in Feit VII.2.11 is one. Identifying this expression
with the number of exceptional characters is the separate cyclic theorem. -/
theorem PrimeOrderInput.localMultiplicity_quotient_eq_one [Fact p.Prime]
    {d : PrimeCongruenceBlockData p G}
    {residue : Localization.AtPrime d.primeIdeal →+* K} {m : ℕ} {P : Sylow p G}
    (h : PrimeOrderInput d residue m P) :
    (Nat.card P - 1) / localInertialIndex (P : Subgroup G)
      (DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G)
        (reducedPrincipal d residue)) = 1 := by
  rw [h.sylow_card, h.inertial_index]
  exact Nat.div_self (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
