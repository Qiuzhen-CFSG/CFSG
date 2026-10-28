module

public import Mathlib.RepresentationTheory.Character
public import Theory.SpecificGroups.SymmetricFourClasses
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Integral representations affording the five ordinary characters of S₄

We construct the trivial and sign representations, the augmentation
representation on the three pair partitions, the augmentation representation
on four letters, and its sign twist. Augmentation matrices use the basis
`e_j - e_last`. Their multiplication laws and integer traces are checked by
kernel reduction on the finite group, before extension of scalars to ℂ.
Irreducibility is proved in `Theory.Character.SymmetricFour` from these traces.

The class order is identity, transposition, double transposition, three-cycle,
and four-cycle. Source: the usual permutation-module construction of the S₄
character table, used in Fong, *Some Sylow subgroups of order 32*,
J. Algebra 6 (1967), p. 71.
-/

public section

open scoped BigOperators
namespace SymmetricFourCharacters

open SymmetricFourClasses
abbrev G := Equiv.Perm (Fin 4)

/-- Dimensions in trivial, sign, degree-two, standard, sign-standard order. -/
@[expose] def degree : Fin 5 → ℕ := ![1, 1, 2, 3, 3]
/-- Integer traces, whose agreement with the representations is proved below. -/
@[expose] def table : Fin 5 → Fin 5 → ℤ :=
  ![![1, 1, 1, 1, 1], ![1, -1, 1, 1, -1], ![2, 0, 2, -1, 0],
    ![3, 1, -1, 0, -1], ![3, -1, -1, 0, 1]]

/-- The fixed-point-free involutions encode the three pair partitions. -/
private def pair : Fin 3 → G :=
  ![Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]
private def pairImage (g : G) (j : Fin 3) : Fin 3 :=
  if g * pair j * g⁻¹ = pair 0 then 0
  else if g * pair j * g⁻¹ = pair 1 then 1 else 2

/-- Action in the basis `e_j - e_last` of a sum-zero permutation module. -/
private def augmentationMatrix {n : ℕ} (f : Fin (n+1) → Fin (n+1)) :
    Matrix (Fin n) (Fin n) ℤ := fun i j =>
  (if f j.castSucc = i.castSucc then 1 else 0) -
  (if f (Fin.last n) = i.castSucc then 1 else 0)
private def intMatrix (i : Fin 5) (g : G) : Matrix (Fin (degree i)) (Fin (degree i)) ℤ :=
  match i with
  | 0 => 1
  | 1 => fun _ _ => (g.sign : ℤ)
  | 2 => augmentationMatrix (pairImage g)
  | 3 => augmentationMatrix g
  | 4 => (g.sign : ℤ) • augmentationMatrix g

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem matrix_one : ∀ i, intMatrix i 1 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem matrix_mul : ∀ i g h, intMatrix i (g*h) = intMatrix i g * intMatrix i h := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem matrix_trace : ∀ i g, (intMatrix i g).trace = table i (classIndex g) := by decide +kernel

/-- The five complex representations obtained from their integral matrices. -/
noncomputable def rep (i : Fin 5) : Representation ℂ G (Fin (degree i) → ℂ) where
  toFun g := Matrix.toLin' ((intMatrix i g).map (Int.castRingHom ℂ))
  map_one' := by rw [matrix_one, Matrix.map_one _ (by simp) (by simp)]; exact Matrix.toLin'_one
  map_mul' g h := by rw [matrix_mul, Matrix.map_mul]; exact Matrix.toLin'_mul _ _

/-- Their characters are the computed integer matrix traces. -/
theorem rep_character (i : Fin 5) (g : G) :
    (rep i).character g = (table i (classIndex g) : ℂ) := by
  change LinearMap.trace ℂ _ (Matrix.toLin' _) = _
  rw [Matrix.trace_toLin'_eq, ← AddMonoidHom.map_trace, matrix_trace]
  rfl

end SymmetricFourCharacters
