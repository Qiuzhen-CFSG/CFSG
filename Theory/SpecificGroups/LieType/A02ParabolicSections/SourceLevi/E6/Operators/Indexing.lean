module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E6.Operators.Coordinates
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Coordinates of the native E₆ Geck basis

The proved root enumeration extends to the six Cartan vectors followed by the
72 root vectors. Integer coordinate equalities detect the native root sums;
the six positive and negative simple roots have explicit indices.
This is the coordinate interface for the integral Geck construction.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace Theory.SpecificGroups.LieType.SourceLevi.E6.Operators
open Coordinates
noncomputable section
open scoped Classical Matrix
local instance : InvolutiveNeg typeE6Roots := typeE6RootPairing.indexNeg
local instance : Fintype typeE6Roots := Fintype.ofFinite _

abbrev Basis := typeE6RootPairing_base.support ⊕ typeE6Roots

def basisEquiv : Fin 78 ≃ Basis :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr typeE6RootPairing_baseEquiv rootEquiv)

def reindex {S : Type*} [CommRing S] :
    Matrix Basis Basis S ≃+* Matrix (Fin 78) (Fin 78) S :=
  Matrix.reindexRingEquiv S basisEquiv.symm

theorem reindex_apply {S : Type*} [CommRing S]
    (A : Matrix Basis Basis S) (r c : Fin 78) :
    reindex A r c = A (basisEquiv r) (basisEquiv c) := rfl

theorem reindex_map {S : Type*} [CommRing S] (A : Matrix Basis Basis ℤ) :
    reindex (A.map (Int.castRingHom S)) = (reindex A).map (Int.castRingHom S) := rfl

theorem reindex_smul {S : Type*} [CommRing S] (s : S) (A : Matrix Basis Basis S) :
    reindex (s • A) = s • reindex A := rfl

def simple : Fin 6 → Fin 72 := ![56, 38, 30, 39, 18, 2]
def negative : Fin 6 → Fin 72 := ![55, 37, 29, 36, 17, 1]

def simpleCoord : Fin 6 → Fin 8 → ℤ :=
  ![![1,-1,-1,-1,-1,-1,-1,1], ![0,0,0,0,0,0,2,-2],
    ![0,0,0,0,0,2,-2,0], ![0,0,0,0,0,0,2,2],
    ![0,0,0,0,2,-2,0,0], ![0,0,0,2,-2,0,0,0]]

theorem coord_simple (i : Fin 6) : coord (simple i) = simpleCoord i := by
  revert i
  decide +kernel

theorem root_simple (i : Fin 6) : root (simple i) = typeE6RootPairing_baseEquiv i := by
  apply Subtype.ext
  ext q
  change (coord (simple i) q : ℝ) / 2 = typeE6SimpleRoot i q
  rw [coord_simple]
  fin_cases i <;> fin_cases q <;>
    norm_num [simpleCoord, typeE6SimpleRoot, typeE8SimpleRoot,
      Matrix.cons_val_succ]

theorem root_eq_add_nsmul_iff (r s t : Fin 72) (n : ℕ) :
    typeE6RootPairing.root (root r) =
      typeE6RootPairing.root (root s) + n • typeE6RootPairing.root (root t) ↔
    coord r = coord s + n • coord t := by
  constructor
  · intro h
    funext q
    have hq := congrArg (fun x : typeE6RootSpan => x.val q) h
    change (coord r q : ℝ) / 2 = (coord s q : ℝ) / 2 + n • ((coord t q : ℝ) / 2) at hq
    simp only [nsmul_eq_mul] at hq ⊢
    change coord r q = coord s q + (n : ℤ) * coord t q
    have h' : (coord r q : ℝ) = (coord s q : ℝ) + n * (coord t q : ℝ) := by linarith
    exact_mod_cast h'
  · intro h
    apply Subtype.ext
    funext q
    have hq := congrFun h q
    change coord r q = coord s q + n • coord t q at hq
    have h' : (coord r q : ℝ) = (coord s q : ℝ) + n * (coord t q : ℝ) := by exact_mod_cast hq
    change (coord r q : ℝ) / 2 = (coord s q : ℝ) / 2 + n • ((coord t q : ℝ) / 2)
    simp only [nsmul_eq_mul]
    linarith

theorem root_negative (i : Fin 6) : root (negative i) = -(typeE6RootPairing_baseEquiv i : typeE6Roots) := by
  apply typeE6RootPairing.root.injective
  rw [RootPairing.indexNeg_neg, typeE6RootPairing.root_reflectionPerm,
    typeE6RootPairing.reflection_apply_self]
  rw [← root_simple]
  apply Subtype.ext
  funext q
  have h : coord (negative i) q = -coord (simple i) q := by
    have hc : ∀ i : Fin 6, coord (negative i) = -coord (simple i) := by decide +kernel
    exact congrFun (hc i) q
  change (coord (negative i) q : ℝ) / 2 = -((coord (simple i) q : ℝ) / 2)
  rw [h, Int.cast_neg]
  ring

end
end Theory.SpecificGroups.LieType.SourceLevi.E6.Operators
