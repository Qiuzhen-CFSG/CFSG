module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock.ResiduePrimitivity
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock.AlgebraicExtension
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock.SylowPrimitivity

/-!
# The actual reduced principal congruence projector

The localized ordinary projector is primitive after reduction to its residue
field by the central-scalar nilpotence argument. Every specified reduction
into the algebraic closure factors through that residue field, and principal
primitivity survives this algebraic extension. Augmentation one therefore
identifies the literal reduction as the principal modular block. Transfer at
a Sylow subgroup proves that its Brauer restriction is also primitive.

Source: Feit, III.8--9. The Sylow correspondence is the principal case of
V.6.2, printed pp.209--210.
-/

public section
noncomputable section
namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree
open ModularBlock ModularBlock.PrimeBlockConstruction
open PrincipalBlock
variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- The literal projector is primitive over the literal algebraic closure. -/
theorem reducedPrincipal_isCentrallyPrimitive (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* AlgebraicClosure (ZMod p)) :
    IsCentrallyPrimitive (reducedPrincipal d residue) := by
  obtain ⟨φ, hφ⟩ := exists_residue_embedding d residue
  let k := residueField d
  let K := AlgebraicClosure (ZMod p)
  let : Algebra k K := φ.toAlgebra
  let : Algebra (ZMod p) k := ZMod.algebra k p
  let : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.tower_top (K := ZMod p) (A := K) k
  have h := map_isCentrallyPrimitive_of_algebraic k K G
    (reducedPrincipal d (toResidue d))
    (reducedPrincipalBlockElement_isCentrallyPrimitive d)
    (reducedPrincipal_augmentation d (toResidue d))
  convert h using 1
  ext g
  exact (RingHom.congr_fun hφ _).symm

/-- The literal Sylow Brauer restriction is primitive over the algebraic closure. -/
theorem reducedPrincipal_sylowBrauer_isCentrallyPrimitive
    (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* AlgebraicClosure (ZMod p))
    (P : Sylow p G) :
    IsCentrallyPrimitive
      (DefectSupport.subgroupCentralizerRestriction (AlgebraicClosure (ZMod p))
        (P : Subgroup G) (reducedPrincipal d residue)) := by
  obtain ⟨φ, hφ⟩ := exists_residue_embedding d residue
  let k := residueField d
  let K := AlgebraicClosure (ZMod p)
  let : Algebra k K := φ.toAlgebra
  let : Algebra (ZMod p) k := ZMod.algebra k p
  let : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.tower_top (K := ZMod p) (A := K) k
  let e := reducedPrincipal d (toResidue d)
  let E := DefectSupport.subgroupCentralizerRestriction k (P : Subgroup G) e
  have heaug : groupAlgebraAugmentation k G e = 1 :=
    reducedPrincipal_augmentation d (toResidue d)
  have hEaug : groupAlgebraAugmentation k (Subgroup.centralizer (P : Set G)) E = 1 :=
    (SubgroupBrauerMap.augmentation_subgroupCentralizerRestriction
      (R := k) (P : Subgroup G) P.isPGroup' e
      (reducedPrincipal_mem_center d (toResidue d))).trans heaug
  have h := map_isCentrallyPrimitive_of_algebraic k K
    (Subgroup.centralizer (P : Set G)) E
    (sylow_brauer_isCentrallyPrimitive e
      (reducedPrincipalBlockElement_isCentrallyPrimitive d) heaug P) hEaug
  convert h using 1
  ext g
  exact (RingHom.congr_fun hφ _).symm

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree
