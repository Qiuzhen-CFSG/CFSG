module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount.Classes
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount.LocalBlock
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount.Centralizer

/-!
# Assembly of the cyclic simple count from local representation theory

The supplied `Decomposition` counts actual ambient simple-module classes.
A bijection with the classes selected by the embedded local Brauer image,
together with the local classification, gives the inertial-index count.
The full-inertia hypothesis then gives `p - 1`.

`Centralizer` proves the unique-simple hypothesis for the local centralizer.
Two source-theory premises remain explicit: Feit VII.1.3 supplies the local
normalizer classification, while VII.3.11--12 supplies the Green-socle correspondence.
The theorems here are conditional assembly, not proofs of VII.2.1. The
unconditional count still requires both premises to be constructed.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
open ModularBlock ModularBlock.PrimeBlockConstruction SimpleCount

variable {K G : Type*} [Field K] [Group G] [Finite G] {p m n : ℕ}
    {d : PrimeCongruenceBlockData p G}
    {residue : Localization.AtPrime d.primeIdeal →+* K} {L : CyclicRootLift K m}

/-- Apply the actual class correspondence and local normalizer classification
to the literal family in `a`. The two source premises remain explicit. -/
theorem simpleCount_eq_of_localCorrespondence
    (a : Decomposition d residue L n) (P : Sylow p G)
    (hcorrespondence : Nonempty (SimpleClass (reducedPrincipal d residue) ≃
      SimpleClass (normalizerSelector d residue P)))
    (hlocal : Nat.card (SimpleClass (normalizerSelector d residue P)) =
      localInertialIndex (P : Subgroup G)
        (DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G)
          (reducedPrincipal d residue))) :
    n = localInertialIndex (P : Subgroup G)
      (DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G)
        (reducedPrincipal d residue)) := by
  obtain ⟨f⟩ := hcorrespondence
  exact (card_simpleClass a).symm.trans ((Nat.card_congr f).trans hlocal)

/-- The intended full-inertia application, conditional only on the two
remaining local representation-theory results above. -/
theorem simpleCount_eq_sub_one_of_localCorrespondence
    (a : Decomposition d residue L n) (P : Sylow p G)
    (h : PrimeOrderInput d residue m P)
    (hcorrespondence : Nonempty (SimpleClass (reducedPrincipal d residue) ≃
      SimpleClass (normalizerSelector d residue P)))
    (hlocal : Nat.card (SimpleClass (normalizerSelector d residue P)) =
      localInertialIndex (P : Subgroup G)
        (DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G)
          (reducedPrincipal d residue))) :
    n = p - 1 :=
  (simpleCount_eq_of_localCorrespondence a P hcorrespondence hlocal).trans h.inertial_index

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
