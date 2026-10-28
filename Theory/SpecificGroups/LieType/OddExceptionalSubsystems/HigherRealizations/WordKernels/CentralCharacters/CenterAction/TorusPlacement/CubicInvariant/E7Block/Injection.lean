module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.CubicInvariant.E7Block.Coordinates
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.AdjointBlocks.Integral
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ResidueDiagonal

/-!
# The literal E7 coordinate inclusion and its residue character

Extension by zero embeds the 27 root coordinates in the actual E7 Chevalley
basis over every commutative ring. The central coroot exponent is checked on
these roots, giving the balanced character -1. Thus the residue diagonal acts
on this concrete copy by the inverse scalar, without a cubic hypothesis.
Source: GLS3 §§1.12.5–6 and §2.6.2, for Aschbacher–Smith A.2.17, p.39.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Matrix
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.E7Block
local instance : Fintype typeE7Roots := Fintype.ofFinite _

/-- The 27 root basis vectors inside the 133-dimensional E7 lattice. -/
def index : Fin 27 ↪ typeE7RootPairing_base.support ⊕ typeE7Roots :=
  root.trans (Function.Embedding.inr)

/-- Extension by zero on the literal root coordinates. -/
def J (R : Type*) [CommRing R] :
    (Fin 27 → R) →ₗ[R] ((typeE7RootPairing_base.support ⊕ typeE7Roots) → R) :=
  (AdjointBlocks.inclusionOver index R).mulVecLin

@[simp] theorem J_index (R : Type*) [CommRing R] (x : Fin 27 → R) (j : Fin 27) :
    J R x (index j) = x j := AdjointBlocks.inclusion_mulVec index R x j

/-- This inclusion is injective over every commutative ring. -/
theorem J_injective (R : Type*) [CommRing R] : Function.Injective (J R) :=
  AdjointBlocks.inclusion_mulVec_injective index R

private theorem pairing_cast (j : Fin 27) (i : Fin 6) :
    (typeE7RootPairing.pairingIn ℤ (root j) (e7Node i) : ℝ) =
      dot (coord j) (typeE7SimpleRoot (i.castLE (by decide))) := by
  change (algebraMap ℤ ℝ) (typeE7RootPairing.pairingIn ℤ (root j) (e7Node i)) = _
  rw [typeE7RootPairing.algebraMap_pairingIn, typeE7RootPairing_pairing]
  rfl

private theorem pairing_four (j : Fin 27) (i : Fin 6) :
    4 * typeE7RootPairing.pairingIn ℤ (root j) (e7Node i) =
      ∑ k, CubicModel.twiceRoot j k * twiceSimple i k := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [pairing_cast]
  simp only [dot, coord, simple_coord, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The unreduced integral central exponents of the 27 coordinates. -/
def exponent : Fin 27 → ℤ :=
  ![2,-1,-1,2,-1,2,-1,2,2,-1,-1,-1,2,-1,2,-1,2,2,-1,-4,-1,-1,-1,-1,2,-1,-1]

private theorem exponent_certificate : ∀ j : Fin 27,
    -((∑ k, CubicModel.twiceRoot j k * twiceSimple 0 k) +
      2 * (∑ k, CubicModel.twiceRoot j k * twiceSimple 1 k) +
      (∑ k, CubicModel.twiceRoot j k * twiceSimple 4 k) +
      2 * (∑ k, CubicModel.twiceRoot j k * twiceSimple 5 k)) = 4 * exponent j := by
  decide +kernel

/-- The exponent uses the actual pairing and the repository's inverse-character convention. -/
theorem centralExponent_index (j : Fin 27) :
    centralExponent e7Node (index j) = exponent j := by
  have h0 := pairing_four j 0
  have h1 := pairing_four j 1
  have h4 := pairing_four j 4
  have h5 := pairing_four j 5
  have he := exponent_certificate j
  change -(typeE7RootPairing.pairingIn ℤ (root j) (e7Node 0) +
    2 * typeE7RootPairing.pairingIn ℤ (root j) (e7Node 1) +
    typeE7RootPairing.pairingIn ℤ (root j) (e7Node 4) +
    2 * typeE7RootPairing.pairingIn ℤ (root j) (e7Node 5)) = exponent j
  omega

/-- All 27 coordinates have balanced central exponent -1. -/
theorem balancedExponent_index (j : Fin 27) :
    balancedResidue (centralExponent e7Node (index j)) = -1 := by
  rw [centralExponent_index]
  have h : ∀ j, balancedResidue (exponent j) = -1 := by decide +kernel
  exact h j

attribute [local instance] Classical.decEq

/-- The literal residue diagonal acts on the constructed copy by the inverse scalar. -/
theorem residueDiagonal_J (F : Type*) [Field F] (u : Fˣ) (x : Fin 27 → F) :
    (residueDiagonal F e7Node u).val *ᵥ J F x = J F ((u⁻¹ : Fˣ).val • x) := by
  ext a
  change (Matrix.diagonal _ *ᵥ (AdjointBlocks.inclusionOver index F *ᵥ x)) a =
    (AdjointBlocks.inclusionOver index F *ᵥ ((u⁻¹ : Fˣ).val • x)) a
  rw [Matrix.mulVec_diagonal]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum,
    AdjointBlocks.inclusionOver_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : a = index j
  · subst a
    simp [balancedExponent_index]
  · simp [h]

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.E7Block
