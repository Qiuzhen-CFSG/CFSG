module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ChevalleySplitTorus
public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
/-!
# Matrix support in the centralizer of the concrete F4 torus

Commuting with the literal diagonal torus forces each matrix coefficient
between different integral weights to vanish. The simple coroots form a basis,
so the forty-eight root weights are distinct and nonzero, in every field
characteristic after evaluation as torus characters. Thus only the Cartan block
and the individual root diagonal entries can remain.

This is the linear algebra step toward maximality of the literal split torus.
It does not assert that every such block matrix in the carrier lies in that
torus: the Cartan block and the relations between root scalars still need to be
determined. Sources: GLS3, Sections 1.4 and 1.9; the diagonal representation in
`F4ChevalleySplitTorus` and the integral Chevalley construction.
-/

public section

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.F4Chevalley
open RootPairing.IntegralGeckConstruction
open scoped BigOperators Matrix
namespace Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy
variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Equality of the torus eigenvalues at every parameter detects the integral weight. -/
theorem basisWeight_eq_of_torusUnit_eq (i j : BasisIndex)
    (h : ∀ u : Fin 4 → kˣ, basisTorusUnit u i = basisTorusUnit u j) :
    torusWeightExponent i = torusWeightExponent j := by
  apply dLaurentCharacter_injective (k := k) 4
  apply Morphism.ext
  funext x
  apply (dPointEquiv 1).injective
  funext q
  have hq : q = 0 := Subsingleton.elim _ _
  subst q
  change dPointEquiv 1 ((dLaurentCharacter (k := k) 4 (torusWeightExponent i)).onPoints x) 0 =
    dPointEquiv 1 ((dLaurentCharacter (k := k) 4 (torusWeightExponent j)).onPoints x) 0
  rw [dLaurentCharacter_apply, dLaurentCharacter_apply]
  exact (basisTorusUnit_formula (dPointEquiv 4 x) i).symm.trans
    ((h _).trans (basisTorusUnit_formula (dPointEquiv 4 x) j))

/-- A matrix commuting with the torus has no entries between distinct weights. -/
theorem matrix_entry_zero_of_commutes_torus
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hA : ∀ u : Fin 4 → kˣ, Commute A (torusElement u))
    (i j : BasisIndex) (hij : torusWeightExponent i ≠ torusWeightExponent j) :
    (A : Matrix BasisIndex BasisIndex k) i j = 0 := by
  by_contra ha
  apply hij
  apply basisWeight_eq_of_torusUnit_eq (k := k)
  intro u
  apply Units.ext
  have he := congrArg (fun B : (Matrix BasisIndex BasisIndex k)ˣ =>
    (B : Matrix BasisIndex BasisIndex k) i j) (hA u).eq
  change ((A : Matrix BasisIndex BasisIndex k) * Matrix.diagonal
      (fun b => (basisTorusUnit u b : k))) i j =
    (Matrix.diagonal (fun b => (basisTorusUnit u b : k)) *
      (A : Matrix BasisIndex BasisIndex k)) i j at he
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm] at he
  exact (mul_right_cancel₀ ha he).symm

/-- Ambient matrix coordinates of a carrier centralizer point commute with every torus matrix. -/
theorem matrix_commutes_torus_of_centralizes
    (g : Variety.Point (Carrier (k := k)))
    (hg : g ∈ (splitTorus (k := k)).centralizer.toSubgroup)
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hA : matrixToAmbient A = (ambientClosedCarrier (k := k)).inclusion.onPoints g)
    (u : Fin 4 → kˣ) : Commute A (torusElement u) := by
  apply (matrixToAmbient_bijective (F := k)).1
  simp only [map_mul, hA]
  let x := (dPointEquiv 4).symm u
  have hx : dPointEquiv 4 x = u := (dPointEquiv 4).apply_symm_apply u
  have ht : matrixToAmbient (torusElement u) =
      (ambientClosedCarrier (k := k)).inclusion.onPoints
        (splitTorusMorphism.onPoints x) := by
    rw [splitTorusMorphism_inclusion_apply, torusAmbientMorphism_matrix, hx]
  rw [ht, ← map_mul, ← map_mul]
  apply congrArg (ambientClosedCarrier (k := k)).inclusion.onPoints
  exact (Subgroup.mem_centralizer_iff.mp hg _ ⟨x, rfl⟩).symm
end Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy
namespace Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy
open Theory.AlgebraicGroup.StandardRootSystem

/-- The simple coroots distinguish the root weights. -/
theorem root_torusWeightExponent_injective :
    Function.Injective (fun r : Root => torusWeightExponent (Sum.inr r)) := by
  intro r s h
  apply typeF4RootPairing.root.injective
  apply typeF4RootPairing.toPerfPair.injective
  apply typeF4RootPairing_base.toCoweightBasis.ext
  intro q
  have hq := congrFun h (typeF4RootPairing_baseEquiv.symm q)
  have hp : typeF4RootPairing.pairingIn ℤ r q =
      typeF4RootPairing.pairingIn ℤ s q := by
    simpa only [torusWeightExponent, basisWeight, chevalleyBasisWeight,
      Equiv.apply_symm_apply, neg_inj] using hq
  simpa only [RootPairing.Base.toCoweightBasis_apply,
    LinearMap.toLinearMap_toPerfPair, RootPairing.root_coroot_eq_pairing,
    RootPairing.algebraMap_pairingIn] using congrArg (algebraMap ℤ ℝ) hp

/-- A root weight is nonzero on the simple-coroot coordinate lattice. -/
theorem root_torusWeightExponent_ne_zero (r : Root) :
    torusWeightExponent (Sum.inr r) ≠ 0 := by
  intro h
  have he : typeF4RootPairing.toPerfPair (typeF4RootPairing.root r) = 0 := by
    apply typeF4RootPairing_base.toCoweightBasis.ext
    intro q
    have hq := congrFun h (typeF4RootPairing_baseEquiv.symm q)
    have hp : typeF4RootPairing.pairingIn ℤ r q = 0 := by
      simpa only [torusWeightExponent, basisWeight, chevalleyBasisWeight,
        Equiv.apply_symm_apply, Pi.zero_apply, neg_eq_zero] using hq
    simpa only [RootPairing.Base.toCoweightBasis_apply,
      LinearMap.toLinearMap_toPerfPair, RootPairing.root_coroot_eq_pairing,
      RootPairing.algebraMap_pairingIn, map_zero, LinearMap.zero_apply] using
      congrArg (algebraMap ℤ ℝ) hp
  have hz : typeF4RootPairing.root r = 0 :=
    typeF4RootPairing.toPerfPair.injective (he.trans (map_zero _).symm)
  exact typeF4RootPairing.ne_zero r hz
end Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy
namespace Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy
open Theory.AlgebraicGroup.StandardRootSystem
variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Each root column of a matrix commuting with the torus is supported on its diagonal. -/
theorem matrix_root_column_support
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hA : ∀ u : Fin 4 → kˣ, Commute A (torusElement u))
    (r : Root) (i : BasisIndex) (hi : i ≠ Sum.inr r) :
    (A : Matrix BasisIndex BasisIndex k) i (Sum.inr r) = 0 := by
  apply matrix_entry_zero_of_commutes_torus A hA
  cases i with
  | inl q =>
      have hq : torusWeightExponent (Sum.inl q) = 0 := by funext j; rfl
      rw [hq]
      exact (root_torusWeightExponent_ne_zero r).symm
  | inr s =>
      exact fun he => hi (congrArg Sum.inr (root_torusWeightExponent_injective he))

/-- Each root row of a matrix commuting with the torus is supported on its diagonal. -/
theorem matrix_root_row_support
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hA : ∀ u : Fin 4 → kˣ, Commute A (torusElement u))
    (r : Root) (i : BasisIndex) (hi : i ≠ Sum.inr r) :
    (A : Matrix BasisIndex BasisIndex k) (Sum.inr r) i = 0 := by
  apply matrix_entry_zero_of_commutes_torus A hA
  cases i with
  | inl q =>
      have hq : torusWeightExponent (Sum.inl q) = 0 := by funext j; rfl
      rw [hq]
      exact root_torusWeightExponent_ne_zero r
  | inr s =>
      exact fun he => hi (congrArg Sum.inr (root_torusWeightExponent_injective he.symm))
end Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy
