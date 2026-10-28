module

public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Elements.X
public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Elements.Y
public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Elements.D0
public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Elements.D1
import Mathlib.Tactic.FinCases

/-!
# Finite permutation equations for the marked J₃ affine configuration

All equations are checked on the 6156-letter action of the actual model,
using packed generators whose equality to the public words is already proved.
Four commuting involutions generate the marked two-subgroup; two commuting
cubic elements normalize it, and the scalar commutes with the two complement
generators. Separating these finite checks allows reuse in the subgroup proofs.

Source: GLS, Number 3, Table 5.3h, printed p.269; Aschbacher--Smith A.2.19,
printed p.41. The retained ATLAS data and untrusted discovery are in `source/`.
-/

namespace Sporadic.Janko3.ThreeCoverConfig
open Theory.GroupTheory OrderCertificate TwoLocal
set_option maxRecDepth 40000
set_option Elab.async false

@[expose] public def qPerm : Fin 4 → Equiv.Perm (Fin 6156)
  | 0 => AffineCertificate.G3
  | 1 => AffineCertificate.G2
  | 2 => AffineCertificate.G1
  | 3 => AffineCertificate.G0

public theorem qPerm_eq (i : Fin 4) :
    qPerm i = (elementaryGenerator i : Equiv.Perm (Fin 6156)) := by
  fin_cases i
  · exact AffineCertificate.G3_eq
  · exact AffineCertificate.G2_eq
  · exact AffineCertificate.G1_eq
  · exact AffineCertificate.G0_eq

public theorem qWord_eq (w : List (Fin 4)) :
    evalWord qPerm w = ((evalWord elementaryGenerator w : Model) : Equiv.Perm (Fin 6156)) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change qPerm i * evalWord qPerm w =
      (elementaryGenerator i : Equiv.Perm (Fin 6156)) *
        ((evalWord elementaryGenerator w : Model) : Equiv.Perm (Fin 6156))
    rw [qPerm_eq, ih]

set_option maxHeartbeats 4000000 in
public theorem elementary_square (i : Fin 4) : elementaryGenerator i ^ 2 = 1 := by
  have h : ∀ j : Fin 4, checkLetters (fun k => decide ((qPerm j ^ 2) k = k)) = true := by
    apply allFin
    decide +kernel
  apply Subtype.ext
  change (elementaryGenerator i : Equiv.Perm (Fin 6156)) ^ 2 = 1
  rw [← qPerm_eq]
  apply Equiv.ext
  exact allLetters _ (h i)

set_option maxHeartbeats 4000000 in
public theorem elementary_commute (i j : Fin 4) :
    Commute (elementaryGenerator i) (elementaryGenerator j) := by
  have h : ∀ a b : Fin 4, checkLetters (fun k =>
      decide ((qPerm a * qPerm b) k = (qPerm b * qPerm a) k)) = true := by
    apply allFin₂
    decide +kernel
  apply Subtype.ext
  change (elementaryGenerator i : Equiv.Perm (Fin 6156)) * elementaryGenerator j =
    (elementaryGenerator j : Equiv.Perm (Fin 6156)) * elementaryGenerator i
  rw [← qPerm_eq, ← qPerm_eq]
  apply Equiv.ext
  exact allLetters _ (h i j)

set_option maxHeartbeats 4000000 in
public theorem x_cube : x ^ 3 = 1 := by
  apply Subtype.ext
  change (x : Equiv.Perm (Fin 6156)) ^ 3 = 1
  rw [← xPerm_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxHeartbeats 4000000 in
public theorem y_cube : y ^ 3 = 1 := by
  apply Subtype.ext
  change (y : Equiv.Perm (Fin 6156)) ^ 3 = 1
  rw [← yPerm_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxHeartbeats 4000000 in
public theorem xy : Commute x y := by
  apply Subtype.ext
  change (x : Equiv.Perm (Fin 6156)) * y = (y : Equiv.Perm (Fin 6156)) * x
  rw [← xPerm_eq, ← yPerm_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxHeartbeats 4000000 in
public theorem xd0 : Commute x d0 := by
  apply Subtype.ext
  change (x : Equiv.Perm (Fin 6156)) * d0 = (d0 : Equiv.Perm (Fin 6156)) * x
  rw [← xPerm_eq, ← d0Perm_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxHeartbeats 4000000 in
public theorem xd1 : Commute x d1 := by
  apply Subtype.ext
  change (x : Equiv.Perm (Fin 6156)) * d1 = (d1 : Equiv.Perm (Fin 6156)) * x
  rw [← xPerm_eq, ← d1Perm_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

@[expose] public def xConjWord : Fin 4 → List (Fin 4)
  | 0 => [0, 2]
  | 1 => [2, 3]
  | 2 => [0]
  | 3 => [0, 1, 2, 3]

@[expose] public def yConjWord : Fin 4 → List (Fin 4)
  | 0 => [2]
  | 1 => [0, 3]
  | 2 => [0, 2]
  | 3 => [0, 1, 2, 3]

set_option maxHeartbeats 4000000 in
public theorem x_conj_elementary (i : Fin 4) :
    x * elementaryGenerator i * x⁻¹ = evalWord elementaryGenerator (xConjWord i) := by
  have h : ∀ j : Fin 4, checkLetters (fun k => decide
      ((xPerm * qPerm j * xPerm⁻¹) k = (evalWord qPerm (xConjWord j)) k)) = true := by
    apply allFin
    decide +kernel
  apply Subtype.ext
  change (x : Equiv.Perm (Fin 6156)) * elementaryGenerator i *
    (x : Equiv.Perm (Fin 6156))⁻¹ = ((evalWord elementaryGenerator (xConjWord i) : Model) : Equiv.Perm (Fin 6156))
  rw [← xPerm_eq, ← qPerm_eq, ← qWord_eq]
  apply Equiv.ext
  exact allLetters _ (h i)

set_option maxHeartbeats 4000000 in
public theorem y_conj_elementary (i : Fin 4) :
    y * elementaryGenerator i * y⁻¹ = evalWord elementaryGenerator (yConjWord i) := by
  have h : ∀ j : Fin 4, checkLetters (fun k => decide
      ((yPerm * qPerm j * yPerm⁻¹) k = (evalWord qPerm (yConjWord j)) k)) = true := by
    apply allFin
    decide +kernel
  apply Subtype.ext
  change (y : Equiv.Perm (Fin 6156)) * elementaryGenerator i *
    (y : Equiv.Perm (Fin 6156))⁻¹ = ((evalWord elementaryGenerator (yConjWord i) : Model) : Equiv.Perm (Fin 6156))
  rw [← yPerm_eq, ← qPerm_eq, ← qWord_eq]
  apply Equiv.ext
  exact allLetters _ (h i)

end Sporadic.Janko3.ThreeCoverConfig
