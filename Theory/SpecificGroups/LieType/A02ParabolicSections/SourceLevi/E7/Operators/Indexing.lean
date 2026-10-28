module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E7.Operators.Coordinates
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Coordinates of the native E7 Geck basis

The proved root enumeration extends to the 7 Cartan vectors followed by the
126 root vectors. Integer coordinate equalities detect the native root sums;
the six positive and negative simple roots have explicit indices.
This is the coordinate interface for the integral Geck construction.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace Theory.SpecificGroups.LieType.SourceLevi.E7.Operators
open Coordinates
noncomputable section
open scoped Classical Matrix
local instance : InvolutiveNeg typeE7Roots := typeE7RootPairing.indexNeg
local instance : Fintype typeE7Roots := Fintype.ofFinite _

abbrev Basis := typeE7RootPairing_base.support ⊕ typeE7Roots

def basisEquiv : Fin 133 ≃ Basis :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr typeE7RootPairing_baseEquiv rootEquiv)

def reindex {S : Type*} [CommRing S] :
    Matrix Basis Basis S ≃+* Matrix (Fin 133) (Fin 133) S :=
  Matrix.reindexRingEquiv S basisEquiv.symm

theorem reindex_apply {S : Type*} [CommRing S]
    (A : Matrix Basis Basis S) (r c : Fin 133) :
    reindex A r c = A (basisEquiv r) (basisEquiv c) := rfl

theorem reindex_map {S : Type*} [CommRing S] (A : Matrix Basis Basis ℤ) :
    reindex (A.map (Int.castRingHom S)) = (reindex A).map (Int.castRingHom S) := rfl

theorem reindex_smul {S : Type*} [CommRing S] (s : S) (A : Matrix Basis Basis S) :
    reindex (s • A) = s • reindex A := rfl

def node (i : Fin 6) : Fin 7 := ⟨i.val, by omega⟩

def simple : Fin 6 → Fin 126 := ![94, 60, 52, 61, 40, 24]
def negative : Fin 6 → Fin 126 := ![93, 59, 51, 58, 39, 23]

def simpleCoord : Fin 6 → Fin 8 → ℤ :=
  ![![1,-1,-1,-1,-1,-1,-1,1], ![0,0,0,0,0,0,2,-2],
    ![0,0,0,0,0,2,-2,0], ![0,0,0,0,0,0,2,2],
    ![0,0,0,0,2,-2,0,0], ![0,0,0,2,-2,0,0,0]]

theorem coord_simple (i : Fin 6) : coord (simple i) = simpleCoord i := by
  revert i
  decide +kernel

theorem root_simple (i : Fin 6) : root (simple i) = typeE7RootPairing_baseEquiv (node i) := by
  apply Subtype.ext
  ext q
  change (coord (simple i) q : ℝ) / 2 = typeE7SimpleRoot (node i) q
  rw [coord_simple]
  fin_cases i <;> fin_cases q <;>
    norm_num [node, simpleCoord, typeE7SimpleRoot, typeE8SimpleRoot,
      Matrix.cons_val_succ]

theorem root_eq_add_nsmul_iff (r s t : Fin 126) (n : ℕ) :
    typeE7RootPairing.root (root r) =
      typeE7RootPairing.root (root s) + n • typeE7RootPairing.root (root t) ↔
    coord r = coord s + n • coord t := by
  constructor
  · intro h
    funext q
    have hq := congrArg (fun x : typeE7Space => x.val q) h
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

theorem root_negative (i : Fin 6) : root (negative i) = -(typeE7RootPairing_baseEquiv (node i) : typeE7Roots) := by
  apply typeE7RootPairing.root.injective
  rw [RootPairing.indexNeg_neg, typeE7RootPairing.root_reflectionPerm,
    typeE7RootPairing.reflection_apply_self]
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
end Theory.SpecificGroups.LieType.SourceLevi.E7.Operators
