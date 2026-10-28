module

public import Theory.Representation.CyclicRootBrauerCharacter
public import Theory.Character.ModularBlock.PrimeIntegralModels
public import Theory.Character.ModularBlock.PrimeSelector
public import Theory.Character.ModularBlock.BrauerCoefficientExtension

/-!
# Root correspondences at the prime defining an ordinary block

The integral root and residue map live over the localization at the actual
prime in `PrimeCongruenceBlockData`. Reduction preserves primitivity for a
prime-to-characteristic root order. This constructs a `CyclicRootLift`
compatible with the integral models, rather than choosing unrelated complex
and modular roots.

The residue map into the literal algebraic closure of the prime field and the
integral models are supplied by `PrimeIntegralModels`. No modular simplicity
or decomposition identity is asserted. Source: Feit, Chapter I, modular
systems and Brauer characters; VII.2 for their cyclic-defect application.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine
open ModularBlock ModularBlock.PrimeBlockConstruction
open ModularBlock.PrincipalBlockConstruction ModularBlock.PrimeIntegralModels
open BlockOrthogonality

variable {p : ℕ} {G : Type*} [Group G] [Finite G]

/-- An integral primitive root and a residue map at the specified block prime. -/
structure CompatibleRoots (d : PrimeCongruenceBlockData p G)
    (K : Type*) [Field K] (m : ℕ) where
  residue : Localization.AtPrime d.primeIdeal →+* K
  root : Localization.AtPrime d.primeIdeal
  primitive : IsPrimitiveRoot root m

namespace CompatibleRoots
variable {d : PrimeCongruenceBlockData p G} {K : Type*} [Field K]
    {m : ℕ} [NeZero m] [NeZero (m : K)]

/-- Use the same integral root for complex extension and modular reduction. -/
@[expose] def lift (r : CompatibleRoots d K m) : CyclicRootLift K m where
  positive := NeZero.pos m
  modularRoot := r.residue r.root
  complexRoot := localizationToComplex d.primeIdeal r.root
  modular_primitive := BrauerCoefficientExtension.primitive_map r.residue r.primitive
  complex_primitive := r.primitive.map_of_injective
    (PrimeIntegralModels.localizationToComplex_injective d.primeIdeal)

end CompatibleRoots

/-- An integral root and a residue map exist for every divisor of the group
order, over the literal algebraic closure of `ZMod p`. The `lift` construction
additionally requires that the root order be nonzero in that field. -/
theorem exists_compatibleRoots (d : PrimeCongruenceBlockData p G)
    [Fact p.Prime] (m : ℕ) (hm : m ∣ Nat.card G) :
    Nonempty (CompatibleRoots d (AlgebraicClosure (ZMod p)) m) := by
  let : d.primeIdeal.IsMaximal := d.primeIdeal_maximal
  obtain ⟨residue⟩ := PrimeIntegralModels.exists_residueMap d.primeIdeal
    (Nat.card_pos (α := G)).ne' d.eta_spec p (PrimeSelector.prime_mem_primeIdeal d)
  obtain ⟨root, hroot⟩ := PrimeSelector.exists_localization_primitiveRoot d m hm
  exact ⟨⟨residue, root, hroot⟩⟩

end Representation.CyclicDefect.PrimeOrderRealLine
