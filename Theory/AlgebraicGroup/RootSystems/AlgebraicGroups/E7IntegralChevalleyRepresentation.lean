module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Tactic
public import Theory.AlgebraicGroup.RootSystems.Exceptional

/-!
# The integral minuscule Chevalley representation of type E7

This module constructs the 56-dimensional minuscule integral lattice for the
standard E7 Cartan datum.  Its root operators are transported from the simple
raising and lowering maps by explicit signed Weyl equivalences.  The resulting
square-zero operators give root curves `1 + tX` over every commutative ring.
Conjugation on the endomorphism lattice gives the adjoint root operator and its
integral second divided power `-X ⊗ Xᵀ`; its root curve is the tensor product
of a minuscule curve with the transpose of its inverse.

Finite certificates check the 126 roots, the 56 minuscule weights, Weyl
stability, and termination of the root-transport route.  The remaining
nilpotence, divided-power, and curve laws are proved symbolically, so they are
valid in every characteristic.  This is the minuscule-lattice construction in
Steinberg, *Lectures on Chevalley Groups*, Theorem 1 and Lemmas 5--6; see also
GLS3, Theorem 1.12.1 and Remark 1.12.10.  No geometric E7 carrier or root-version
classification is used.
-/

@[expose] public section

open scoped BigOperators Kronecker Matrix

namespace Theory.AlgebraicGroup.E7Chevalley

public abbrev RootCoord := Fin 7 → ℤ
public abbrev WeightCoord := Fin 7 → ℤ

public def cartan : Matrix (Fin 7) (Fin 7) ℤ :=
  fun i j => if i = j then 2 else if
    (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
    (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
    (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
    (i.val = 2 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 2) ∨
    (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) ∨
    (i.val = 5 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5)
    then -1 else 0

public theorem cartan_eq_typeE7CartanMatrix :
    cartan = StandardRootSystem.typeE7CartanMatrix := rfl

public def simpleRootCoord (i : Fin 7) : RootCoord := fun j => if i = j then 1 else 0

public def simpleRootWeightCoord (i : Fin 7) : WeightCoord :=
  fun j => cartan i j

public def rootPairing (c : RootCoord) (i : Fin 7) : ℤ :=
  ∑ j, c j * cartan j i

public def reflectRootCoord (i : Fin 7) (c : RootCoord) : RootCoord :=
  fun j => c j - rootPairing c i * if i = j then 1 else 0

public def reflectWeightCoord (i : Fin 7) (c : WeightCoord) : WeightCoord :=
  fun j => c j - c i * cartan i j

public def positiveRootList : List RootCoord :=
  [![0, 0, 0, 0, 0, 0, 1],
   ![0, 0, 0, 0, 0, 1, 0],
   ![0, 0, 0, 0, 0, 1, 1],
   ![0, 0, 0, 0, 1, 0, 0],
   ![0, 0, 0, 0, 1, 1, 0],
   ![0, 0, 0, 0, 1, 1, 1],
   ![0, 0, 0, 1, 0, 0, 0],
   ![0, 0, 1, 0, 0, 0, 0],
   ![0, 0, 1, 0, 1, 0, 0],
   ![0, 0, 1, 0, 1, 1, 0],
   ![0, 0, 1, 0, 1, 1, 1],
   ![0, 0, 1, 1, 0, 0, 0],
   ![0, 0, 1, 1, 1, 0, 0],
   ![0, 0, 1, 1, 1, 1, 0],
   ![0, 0, 1, 1, 1, 1, 1],
   ![0, 1, 0, 0, 0, 0, 0],
   ![0, 1, 1, 0, 0, 0, 0],
   ![0, 1, 1, 0, 1, 0, 0],
   ![0, 1, 1, 0, 1, 1, 0],
   ![0, 1, 1, 0, 1, 1, 1],
   ![0, 1, 1, 1, 0, 0, 0],
   ![0, 1, 1, 1, 1, 0, 0],
   ![0, 1, 1, 1, 1, 1, 0],
   ![0, 1, 1, 1, 1, 1, 1],
   ![0, 1, 2, 1, 1, 0, 0],
   ![0, 1, 2, 1, 1, 1, 0],
   ![0, 1, 2, 1, 1, 1, 1],
   ![0, 1, 2, 1, 2, 1, 0],
   ![0, 1, 2, 1, 2, 1, 1],
   ![0, 1, 2, 1, 2, 2, 1],
   ![1, 0, 0, 0, 0, 0, 0],
   ![1, 1, 0, 0, 0, 0, 0],
   ![1, 1, 1, 0, 0, 0, 0],
   ![1, 1, 1, 0, 1, 0, 0],
   ![1, 1, 1, 0, 1, 1, 0],
   ![1, 1, 1, 0, 1, 1, 1],
   ![1, 1, 1, 1, 0, 0, 0],
   ![1, 1, 1, 1, 1, 0, 0],
   ![1, 1, 1, 1, 1, 1, 0],
   ![1, 1, 1, 1, 1, 1, 1],
   ![1, 1, 2, 1, 1, 0, 0],
   ![1, 1, 2, 1, 1, 1, 0],
   ![1, 1, 2, 1, 1, 1, 1],
   ![1, 1, 2, 1, 2, 1, 0],
   ![1, 1, 2, 1, 2, 1, 1],
   ![1, 1, 2, 1, 2, 2, 1],
   ![1, 2, 2, 1, 1, 0, 0],
   ![1, 2, 2, 1, 1, 1, 0],
   ![1, 2, 2, 1, 1, 1, 1],
   ![1, 2, 2, 1, 2, 1, 0],
   ![1, 2, 2, 1, 2, 1, 1],
   ![1, 2, 2, 1, 2, 2, 1],
   ![1, 2, 3, 1, 2, 1, 0],
   ![1, 2, 3, 1, 2, 1, 1],
   ![1, 2, 3, 1, 2, 2, 1],
   ![1, 2, 3, 1, 3, 2, 1],
   ![1, 2, 3, 2, 2, 1, 0],
   ![1, 2, 3, 2, 2, 1, 1],
   ![1, 2, 3, 2, 2, 2, 1],
   ![1, 2, 3, 2, 3, 2, 1],
   ![1, 2, 4, 2, 3, 2, 1],
   ![1, 3, 4, 2, 3, 2, 1],
   ![2, 3, 4, 2, 3, 2, 1]]

public def rootFinset : Finset RootCoord :=
  positiveRootList.toFinset ∪ (positiveRootList.map fun c => -c).toFinset

public def positiveMinusculeWeightList : List WeightCoord :=
  [![0, 0, 0, 0, 0, 0, 1],
   ![0, 0, 0, 0, 0, 1, -1],
   ![0, 0, 0, 0, 1, -1, 0],
   ![0, 0, 0, 1, -1, 0, 1],
   ![0, 0, 0, 1, -1, 1, -1],
   ![0, 0, 0, 1, 0, -1, 0],
   ![0, 0, 1, -1, -1, 0, 1],
   ![0, 0, 1, -1, -1, 1, -1],
   ![0, 0, 1, -1, 0, -1, 0],
   ![0, 0, 1, 0, -1, 0, 0],
   ![0, 1, -1, 0, 0, 0, 1],
   ![0, 1, -1, 0, 0, 1, -1],
   ![0, 1, -1, 0, 1, -1, 0],
   ![0, 1, -1, 1, 0, 0, 0],
   ![0, 1, 0, -1, 0, 0, 0],
   ![0, 1, 0, 0, -1, 0, 0],
   ![1, -1, 0, 0, 0, 0, 1],
   ![1, -1, 0, 0, 0, 1, -1],
   ![1, -1, 0, 0, 1, -1, 0],
   ![1, -1, 0, 1, 0, 0, 0],
   ![1, -1, 1, -1, 0, 0, 0],
   ![1, -1, 1, 0, -1, 0, 0],
   ![1, 0, -1, 0, 1, 0, 0],
   ![1, 0, -1, 1, 0, 0, 0],
   ![1, 0, 0, -1, 0, 0, 0],
   ![1, 0, 0, 0, -1, 1, 0],
   ![1, 0, 0, 0, 0, -1, 1],
   ![1, 0, 0, 0, 0, 0, -1]]

public def minusculeWeightFinset : Finset WeightCoord :=
  positiveMinusculeWeightList.toFinset ∪
    (positiveMinusculeWeightList.map fun c => -c).toFinset

private theorem orbitCertificate :
    rootFinset.card = 126 ∧
    minusculeWeightFinset.card = 56 ∧
    (∀ (r : rootFinset) (i : Fin 7), reflectRootCoord i r.1 ∈ rootFinset) ∧
    (∀ (w : minusculeWeightFinset) (i : Fin 7),
      reflectWeightCoord i w.1 ∈ minusculeWeightFinset) ∧
    (∀ (w : minusculeWeightFinset) (i : Fin 7),
      w.1 i = -1 ∨ w.1 i = 0 ∨ w.1 i = 1) ∧
    (∀ r : rootFinset, -r.1 ∈ rootFinset) ∧
    (∀ i : Fin 7, simpleRootCoord i ∈ rootFinset) ∧
    (∀ i : Fin 7, ∃ w : minusculeWeightFinset, w.1 i = 1) := by
  decide +kernel

public theorem rootFinset_card : rootFinset.card = 126 := orbitCertificate.1

public theorem minusculeWeightFinset_card : minusculeWeightFinset.card = 56 :=
  orbitCertificate.2.1

public theorem reflectRootCoord_mem (r : rootFinset) (i : Fin 7) :
    reflectRootCoord i r.1 ∈ rootFinset := orbitCertificate.2.2.1 r i

public theorem reflectWeightCoord_mem (w : minusculeWeightFinset) (i : Fin 7) :
    reflectWeightCoord i w.1 ∈ minusculeWeightFinset := orbitCertificate.2.2.2.1 w i

public theorem minusculeWeight_coordinate (w : minusculeWeightFinset) (i : Fin 7) :
    w.1 i = -1 ∨ w.1 i = 0 ∨ w.1 i = 1 := orbitCertificate.2.2.2.2.1 w i

public theorem simpleRootCoord_mem (i : Fin 7) : simpleRootCoord i ∈ rootFinset :=
  orbitCertificate.2.2.2.2.2.2.1 i

public theorem negRootCoord_mem (r : rootFinset) : -r.1 ∈ rootFinset :=
  orbitCertificate.2.2.2.2.2.1 r

private theorem minusculeWeight_coordinate_one_exists (i : Fin 7) :
    ∃ w : minusculeWeightFinset, w.1 i = 1 := orbitCertificate.2.2.2.2.2.2.2 i

public abbrev Root := rootFinset
public abbrev MinusculeWeight := minusculeWeightFinset

public def simpleRoot (i : Fin 7) : Root :=
  ⟨simpleRootCoord i, simpleRootCoord_mem i⟩

public def reflectRoot (i : Fin 7) (r : Root) : Root :=
  ⟨reflectRootCoord i r.1, reflectRootCoord_mem r i⟩

public def negRoot (r : Root) : Root :=
  ⟨-r.1, negRootCoord_mem r⟩

public instance : Neg Root := ⟨negRoot⟩

public def reflectWeight (i : Fin 7) (w : MinusculeWeight) : MinusculeWeight :=
  ⟨reflectWeightCoord i w.1, reflectWeightCoord_mem w i⟩

@[simp] public theorem reflectWeight_coord_self (i : Fin 7) (w : MinusculeWeight) :
    (reflectWeight i w).1 i = -w.1 i := by
  simp [reflectWeight, reflectWeightCoord, cartan]
  ring_nf

@[simp] public theorem reflectWeight_involutive (i : Fin 7) (w : MinusculeWeight) :
    reflectWeight i (reflectWeight i w) = w := by
  apply Subtype.ext
  funext j
  simp [reflectWeight, reflectWeightCoord]
  rw [show cartan i i = 2 by simp [cartan]]
  ring

public abbrev MinusculeLattice := MinusculeWeight → ℤ

public def simpleE (i : Fin 7) : Module.End ℤ MinusculeLattice where
  toFun v w := if w.1 i = 1 then v (reflectWeight i w) else 0
  map_add' x y := by
    funext w
    split <;> simp_all
  map_smul' z x := by
    funext w
    split <;> simp_all

public def simpleF (i : Fin 7) : Module.End ℤ MinusculeLattice where
  toFun v w := if w.1 i = -1 then v (reflectWeight i w) else 0
  map_add' x y := by
    funext w
    split <;> simp_all
  map_smul' z x := by
    funext w
    split <;> simp_all

@[simp] public theorem simpleE_sq_apply (i : Fin 7) (v : MinusculeLattice) :
    simpleE i (simpleE i v) = 0 := by
  funext w
  simp [simpleE]
  omega

@[simp] public theorem simpleF_sq_apply (i : Fin 7) (v : MinusculeLattice) :
    simpleF i (simpleF i v) = 0 := by
  funext w
  simp [simpleF]
  omega

public def simpleWeyl (i : Fin 7) : MinusculeLattice ≃ₗ[ℤ] MinusculeLattice where
  toFun v w := if w.1 i = -1 then -v (reflectWeight i w) else v (reflectWeight i w)
  invFun v w := if w.1 i = 1 then -v (reflectWeight i w) else v (reflectWeight i w)
  left_inv v := by
    funext w
    rcases minusculeWeight_coordinate w i with h | h | h <;> simp [h]
  right_inv v := by
    funext w
    rcases minusculeWeight_coordinate w i with h | h | h <;> simp [h]
  map_add' x y := by
    funext w
    split <;> simp_all [add_comm]
  map_smul' z x := by
    funext w
    split <;> simp_all

public def simpleIndices : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

public def simpleIndexCoord? (r : RootCoord) : Option (Fin 7) :=
  simpleIndices.find? fun i => r = simpleRootCoord i

public def negSimpleIndexCoord? (r : RootCoord) : Option (Fin 7) :=
  simpleIndices.find? fun i => r = -simpleRootCoord i

public def simpleIndex? (r : Root) : Option (Fin 7) :=
  simpleIndexCoord? r.1

public def negSimpleIndex? (r : Root) : Option (Fin 7) :=
  negSimpleIndexCoord? r.1

public def rootCoordIsPositive (r : RootCoord) : Bool := decide (∀ i, 0 ≤ r i)

public def rootIsPositive (r : Root) : Bool := rootCoordIsPositive r.1

public def descentIndexCoord (r : RootCoord) : Fin 7 :=
  ((simpleIndices.find? fun i =>
    if rootCoordIsPositive r then rootPairing r i = 1 else rootPairing r i = -1).getD 0)

public def descentIndex (r : Root) : Fin 7 :=
  descentIndexCoord r.1

public def rootOperatorAux : Nat → Root → Module.End ℤ MinusculeLattice
  | 0, _ => 0
  | n + 1, r =>
      match simpleIndex? r with
      | some i => simpleE i
      | none =>
          match negSimpleIndex? r with
          | some i => simpleF i
          | none =>
              let i := descentIndex r
              (simpleWeyl i).symm.toLinearMap.comp
                ((rootOperatorAux n (reflectRoot i r)).comp (simpleWeyl i).toLinearMap)

public theorem rootOperatorAux_sq_apply (n : Nat) (r : Root) (v : MinusculeLattice) :
    rootOperatorAux n r (rootOperatorAux n r v) = 0 := by
  induction n generalizing r v with
  | zero => rfl
  | succ n ih =>
      rw [rootOperatorAux]
      split
      · exact simpleE_sq_apply _ _
      · split
        · exact simpleF_sq_apply _ _
        · simp only [LinearMap.comp_apply]
          change (simpleWeyl (descentIndex r)).symm
            ((rootOperatorAux n (reflectRoot (descentIndex r) r))
              ((simpleWeyl (descentIndex r))
                ((simpleWeyl (descentIndex r)).symm
                  ((rootOperatorAux n (reflectRoot (descentIndex r) r))
                    ((simpleWeyl (descentIndex r)) v))))) = 0
          rw [(simpleWeyl _).apply_symm_apply]
          rw [ih]
          simp

public def rootOperator (r : Root) : Module.End ℤ MinusculeLattice :=
  rootOperatorAux 18 r

public theorem rootOperator_sq_apply (r : Root) (v : MinusculeLattice) :
    rootOperator r (rootOperator r v) = 0 :=
  rootOperatorAux_sq_apply 18 r v

public abbrev MinusculeMatrix := Matrix MinusculeWeight MinusculeWeight ℤ

public def rootOperatorMatrix (r : Root) : MinusculeMatrix :=
  LinearMap.toMatrix' (rootOperator r)

private def delta (w : MinusculeWeight) : MinusculeLattice :=
  fun v => if v = w then 1 else 0

private theorem minusculeWeight_coordinate_neg_one_exists (i : Fin 7) :
    ∃ w : MinusculeWeight, w.1 i = -1 := by
  rcases minusculeWeight_coordinate_one_exists i with ⟨w, hw⟩
  exact ⟨reflectWeight i w, by simp [hw]⟩

private theorem simpleE_ne_zero (i : Fin 7) : simpleE i ≠ 0 := by
  rcases minusculeWeight_coordinate_one_exists i with ⟨w, hw⟩
  intro h
  have hv := congrArg (fun f : Module.End ℤ MinusculeLattice =>
    f (delta (reflectWeight i w))) h
  have hvw := congrFun hv w
  simp [simpleE, delta, hw] at hvw

private theorem simpleF_ne_zero (i : Fin 7) : simpleF i ≠ 0 := by
  rcases minusculeWeight_coordinate_neg_one_exists i with ⟨w, hw⟩
  intro h
  have hv := congrArg (fun f : Module.End ℤ MinusculeLattice =>
    f (delta (reflectWeight i w))) h
  have hvw := congrFun hv w
  simp [simpleF, delta, hw] at hvw

private theorem conjugate_ne_zero
    (e : MinusculeLattice ≃ₗ[ℤ] MinusculeLattice)
    (f : Module.End ℤ MinusculeLattice) (hf : f ≠ 0) :
    e.symm.toLinearMap.comp (f.comp e.toLinearMap) ≠ 0 := by
  intro h
  apply hf
  apply LinearMap.ext
  intro v
  have hv := congrArg (fun g : Module.End ℤ MinusculeLattice => g (e.symm v)) h
  change e.symm (f (e (e.symm v))) = 0 at hv
  rw [e.apply_symm_apply] at hv
  have hev := congrArg e hv
  simpa using hev

private def rootRouteCompleteAux : Nat → Root → Bool
  | 0, _ => false
  | n + 1, r =>
      match simpleIndex? r with
      | some _ => true
      | none =>
          match negSimpleIndex? r with
          | some _ => true
          | none => rootRouteCompleteAux n (reflectRoot (descentIndex r) r)

private theorem rootRouteComplete (r : Root) : rootRouteCompleteAux 18 r = true := by
  decide +kernel +revert

private theorem rootOperatorAux_ne_zero_of_complete (n : Nat) (r : Root)
    (h : rootRouteCompleteAux n r = true) : rootOperatorAux n r ≠ 0 := by
  induction n generalizing r with
  | zero => simp [rootRouteCompleteAux] at h
  | succ n ih =>
      cases hs : simpleIndex? r with
      | some i =>
          simpa [rootOperatorAux, hs] using simpleE_ne_zero i
      | none =>
          cases hn : negSimpleIndex? r with
          | some i =>
              simpa [rootOperatorAux, hs, hn] using simpleF_ne_zero i
          | none =>
              simp only [rootRouteCompleteAux, hs, hn] at h
              simp only [rootOperatorAux, hs, hn]
              exact conjugate_ne_zero (simpleWeyl (descentIndex r)) _ (ih _ h)

public theorem rootOperator_ne_zero (r : Root) : rootOperator r ≠ 0 :=
  rootOperatorAux_ne_zero_of_complete 18 r (rootRouteComplete r)

public theorem rootOperatorMatrix_ne_zero (r : Root) : rootOperatorMatrix r ≠ 0 := by
  intro h
  apply rootOperator_ne_zero r
  have hh := congrArg Matrix.toLin' h
  simpa [rootOperatorMatrix] using hh

public theorem rootOperatorMatrix_sq (r : Root) :
    rootOperatorMatrix r * rootOperatorMatrix r = 0 := by
  change LinearMap.toMatrix' (rootOperator r) * LinearMap.toMatrix' (rootOperator r) = 0
  rw [← LinearMap.toMatrix'_comp]
  rw [show (rootOperator r).comp (rootOperator r) = 0 by
    apply LinearMap.ext
    intro v
    exact rootOperator_sq_apply r v]
  simp

public def baseChangeRootOperator (R : Type) [CommRing R] (r : Root) :
    Matrix MinusculeWeight MinusculeWeight R :=
  (rootOperatorMatrix r).map (Int.castRingHom R)

public theorem baseChangeRootOperator_sq (R : Type) [CommRing R] (r : Root) :
    baseChangeRootOperator R r * baseChangeRootOperator R r = 0 := by
  change (rootOperatorMatrix r).map (Int.castRingHom R) *
    (rootOperatorMatrix r).map (Int.castRingHom R) = 0
  rw [← Matrix.map_mul]
  rw [rootOperatorMatrix_sq]
  simp

public def minusculeRootCurve (R : Type) [CommRing R] (r : Root) (t : R) :
    Matrix MinusculeWeight MinusculeWeight R :=
  1 + t • baseChangeRootOperator R r

@[simp] public theorem minusculeRootCurve_zero (R : Type) [CommRing R] (r : Root) :
    minusculeRootCurve R r 0 = 1 := by
  simp [minusculeRootCurve]

public theorem minusculeRootCurve_add (R : Type) [CommRing R]
    (r : Root) (t u : R) :
    minusculeRootCurve R r t * minusculeRootCurve R r u =
      minusculeRootCurve R r (t + u) := by
  simp only [minusculeRootCurve, add_mul, mul_add, one_mul, mul_one]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, baseChangeRootOperator_sq]
  simp [add_smul]
  abel

public theorem minusculeRootCurve_neg_mul (R : Type) [CommRing R]
    (r : Root) (t : R) :
    minusculeRootCurve R r (-t) * minusculeRootCurve R r t = 1 := by
  rw [minusculeRootCurve_add]
  simp

public theorem minusculeRootCurve_mul_neg (R : Type) [CommRing R]
    (r : Root) (t : R) :
    minusculeRootCurve R r t * minusculeRootCurve R r (-t) = 1 := by
  rw [minusculeRootCurve_add]
  simp

public abbrev AdjointIndex := MinusculeWeight × MinusculeWeight

public def adjointRootOperator (R : Type) [CommRing R] (r : Root) :
    Matrix AdjointIndex AdjointIndex R :=
  baseChangeRootOperator R r ⊗ₖ (1 : Matrix MinusculeWeight MinusculeWeight R) -
    (1 : Matrix MinusculeWeight MinusculeWeight R) ⊗ₖ (baseChangeRootOperator R r)ᵀ

public def adjointRootDividedPowerTwo (R : Type) [CommRing R] (r : Root) :
    Matrix AdjointIndex AdjointIndex R :=
  -(baseChangeRootOperator R r ⊗ₖ (baseChangeRootOperator R r)ᵀ)

public theorem adjointRootOperator_sq (R : Type) [CommRing R] (r : Root) :
    adjointRootOperator R r * adjointRootOperator R r =
      2 • adjointRootDividedPowerTwo R r := by
  let X := baseChangeRootOperator R r
  have hX : X * X = 0 := baseChangeRootOperator_sq R r
  have hXX : Xᵀ * Xᵀ = 0 := by
    rw [← Matrix.transpose_mul, hX]
    simp
  have hleft :
      (X ⊗ₖ (1 : Matrix MinusculeWeight MinusculeWeight R)) * (X ⊗ₖ 1) = 0 := by
    rw [← Matrix.mul_kronecker_mul, hX]
    simp
  have hright :
      ((1 : Matrix MinusculeWeight MinusculeWeight R) ⊗ₖ Xᵀ) * (1 ⊗ₖ Xᵀ) = 0 := by
    rw [← Matrix.mul_kronecker_mul, hXX]
    simp
  have hcross₁ :
      (X ⊗ₖ (1 : Matrix MinusculeWeight MinusculeWeight R)) * (1 ⊗ₖ Xᵀ) = X ⊗ₖ Xᵀ := by
    rw [← Matrix.mul_kronecker_mul]
    simp
  have hcross₂ :
      ((1 : Matrix MinusculeWeight MinusculeWeight R) ⊗ₖ Xᵀ) * (X ⊗ₖ 1) = X ⊗ₖ Xᵀ := by
    rw [← Matrix.mul_kronecker_mul]
    simp
  change (X ⊗ₖ (1 : Matrix MinusculeWeight MinusculeWeight R) - 1 ⊗ₖ Xᵀ) *
      (X ⊗ₖ 1 - 1 ⊗ₖ Xᵀ) = 2 • (-(X ⊗ₖ Xᵀ))
  rw [sub_mul, mul_sub, mul_sub, hleft, hright, hcross₁, hcross₂]
  module

public def adjointRootCurve (R : Type) [CommRing R] (r : Root) (t : R) :
    Matrix AdjointIndex AdjointIndex R :=
  minusculeRootCurve R r t ⊗ₖ (minusculeRootCurve R r (-t))ᵀ

public theorem adjointRootCurve_taylor (R : Type) [CommRing R]
    (r : Root) (t : R) :
    adjointRootCurve R r t =
      1 + t • adjointRootOperator R r + t ^ 2 • adjointRootDividedPowerTwo R r := by
  ext ⟨a, b⟩ ⟨c, d⟩
  by_cases hac : a = c <;> by_cases hbd : b = d <;>
    simp [adjointRootCurve, minusculeRootCurve, adjointRootOperator,
      adjointRootDividedPowerTwo, Matrix.kroneckerMap_apply, hac, hbd] <;>
    ring

@[simp] public theorem adjointRootCurve_zero (R : Type) [CommRing R] (r : Root) :
    adjointRootCurve R r 0 = 1 := by
  simp [adjointRootCurve]

public theorem adjointRootCurve_add (R : Type) [CommRing R]
    (r : Root) (t u : R) :
    adjointRootCurve R r t * adjointRootCurve R r u = adjointRootCurve R r (t + u) := by
  simp only [adjointRootCurve]
  rw [← Matrix.mul_kronecker_mul]
  rw [minusculeRootCurve_add]
  rw [← Matrix.transpose_mul]
  rw [minusculeRootCurve_add]
  rw [show -u + -t = -(t + u) by ring]

public theorem adjointRootCurve_neg_mul (R : Type) [CommRing R]
    (r : Root) (t : R) :
    adjointRootCurve R r (-t) * adjointRootCurve R r t = 1 := by
  rw [adjointRootCurve_add]
  simp

public theorem adjointRootCurve_mul_neg (R : Type) [CommRing R]
    (r : Root) (t : R) :
    adjointRootCurve R r t * adjointRootCurve R r (-t) = 1 := by
  rw [adjointRootCurve_add]
  simp

/-- The minuscule root curve as a matrix unit, with inverse parameter `-t`. -/
public def minusculeRootCurveUnit {R : Type} [CommRing R] (r : Root) (t : R) :
    (Matrix MinusculeWeight MinusculeWeight R)ˣ where
  val := minusculeRootCurve R r t
  inv := minusculeRootCurve R r (-t)
  val_inv := minusculeRootCurve_mul_neg R r t
  inv_val := minusculeRootCurve_neg_mul R r t

/-- The adjoint root curve as a matrix unit, with inverse parameter `-t`. -/
public def adjointRootCurveUnit {R : Type} [CommRing R] (r : Root) (t : R) :
    (Matrix AdjointIndex AdjointIndex R)ˣ where
  val := adjointRootCurve R r t
  inv := adjointRootCurve R r (-t)
  val_inv := adjointRootCurve_mul_neg R r t
  inv_val := adjointRootCurve_neg_mul R r t

public def minusculeRootGenerator {R : Type} [CommRing R] (p : Root × R) :
    (Matrix MinusculeWeight MinusculeWeight R)ˣ :=
  minusculeRootCurveUnit p.1 p.2

public def adjointRootGenerator {R : Type} [CommRing R] (p : Root × R) :
    (Matrix AdjointIndex AdjointIndex R)ˣ :=
  adjointRootCurveUnit p.1 p.2

/-- The generators used by the simply connected minuscule E7 carrier. -/
public def minusculeRootGenerators {R : Type} [CommRing R] :
    Set ((Matrix MinusculeWeight MinusculeWeight R)ˣ) :=
  Set.range minusculeRootGenerator

/-- The generators used by the adjoint E7 carrier. -/
public def adjointRootGenerators {R : Type} [CommRing R] :
    Set ((Matrix AdjointIndex AdjointIndex R)ˣ) :=
  Set.range adjointRootGenerator

/-- The integral operators and divided powers consumed by the E7 carrier construction. -/
public structure IntegralModel where
  minusculeRootOperator : Root → MinusculeMatrix
  minuscule_sq : ∀ r, minusculeRootOperator r * minusculeRootOperator r = 0
  minuscule_ne_zero : ∀ r, minusculeRootOperator r ≠ 0
  adjointRootOperator : Root → Matrix AdjointIndex AdjointIndex ℤ
  adjointDividedPowerTwo : Root → Matrix AdjointIndex AdjointIndex ℤ
  adjoint_sq : ∀ r,
    adjointRootOperator r * adjointRootOperator r = 2 • adjointDividedPowerTwo r

/-- The certified integral E7 minuscule and adjoint representation data. -/
public def integralModel : IntegralModel where
  minusculeRootOperator := rootOperatorMatrix
  minuscule_sq := rootOperatorMatrix_sq
  minuscule_ne_zero := rootOperatorMatrix_ne_zero
  adjointRootOperator := adjointRootOperator ℤ
  adjointDividedPowerTwo := adjointRootDividedPowerTwo ℤ
  adjoint_sq := adjointRootOperator_sq ℤ

public def typeE7IntegralChevalleyModel : IntegralModel := integralModel

/-- A checked characteristic-free integral E7 Chevalley representation exists. -/
public theorem typeE7_integralChevalleyRepresentation_exists : Nonempty IntegralModel :=
  ⟨typeE7IntegralChevalleyModel⟩

end Theory.AlgebraicGroup.E7Chevalley
