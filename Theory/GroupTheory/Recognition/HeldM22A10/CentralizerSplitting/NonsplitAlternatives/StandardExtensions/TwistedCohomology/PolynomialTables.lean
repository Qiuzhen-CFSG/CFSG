module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.TwistedCohomology.Coordinates
public import Mathlib.Algebra.BigOperators.Fin
/-!
# Binary polynomial certificates for normalized twisted cocycles

A 100-bit vector denotes a linear polynomial in the 100 non-tree cocycle
coordinates. Evaluation turns bitwise XOR into addition in `ZMod 2`. The
word-reconstruction polynomials therefore evaluate to the actual factor-set
table. In particular each polynomial `equation s t u i` vanishes for the
coordinates of a normalized cocycle.

All action coefficients are checked on the sixteen binary vectors by the
kernel. No rank or cohomology dimension is assumed. Source context:
Huppert--Blackburn III, XII.1.18(b), p.314.
-/

@[expose] public section

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions.TwistedCohomology
open LocalModelDichotomy AbelianExtension
open scoped BigOperators

abbrev Poly := BitVec 100

def value (x : Fin 100 → ZMod 2) (p : Poly) : ZMod 2 :=
  ∑ i, if p.getLsbD i.val then x i else 0

theorem value_zero (x : Fin 100 → ZMod 2) : value x 0 = 0 := by simp [value]

theorem value_xor (x : Fin 100 → ZMod 2) (p q : Poly) :
    value x (p ^^^ q) = value x p + value x q := by
  rw [value, value, value, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases p.getLsbD i.val <;> cases q.getLsbD i.val <;>
    simp [CharTwo.add_self_eq_zero]

def atom (k : Fin 100) : Poly := (1 : Poly) <<< k.val

theorem atom_bits : ∀ k i : Fin 100,
    (atom k).getLsbD i.val = decide (i = k) := by decide +kernel

theorem value_atom (x : Fin 100 → ZMod 2) (k : Fin 100) : value x (atom k) = x k := by
  simp only [value, atom_bits]
  simp

theorem value_eq_of_xor_zero (x : Fin 100 → ZMod 2) (p q : Poly)
    (h : value x (p ^^^ q) = 0) : value x p = value x q := by
  rw [value_xor, CharTwo.add_eq_zero] at h
  exact h

theorem value_xor_zero (x : Fin 100 → ZMod 2) {p q : Poly}
    (hp : value x p = 0) (hq : value x q = 0) : value x (p ^^^ q) = 0 := by
  rw [value_xor, hp, hq, add_zero]

def sumPoly : List Poly → Poly := List.foldr (· ^^^ ·) 0

theorem value_sumPoly (x : Fin 100 → ZMod 2) (l : List Poly) :
    value x (sumPoly l) = (l.map (value x)).sum := by
  induction l with
  | nil => exact value_zero x
  | cons p l ih =>
    change value x (p ^^^ sumPoly l) = value x p + (l.map (value x)).sum
    rw [value_xor, ih]

def actionIndices : Fin 24 → Fin 4 → List (Fin 4) := ![![[0], [1], [2], [3]], ![[1, 2, 3], [0, 2, 3], [0, 1, 2], [0, 1, 3]], ![[1, 2, 3], [0, 1, 3], [0, 2, 3], [0, 1, 2]], ![[0], [3], [1], [2]], ![[0], [2], [3], [1]], ![[1, 2, 3], [0, 1, 2], [0, 1, 3], [0, 2, 3]], ![[0, 2, 3], [1, 2, 3], [0, 1, 3], [0, 1, 2]], ![[1], [0], [3], [2]], ![[2], [0], [1], [3]], ![[0, 1, 2], [1, 2, 3], [0, 2, 3], [0, 1, 3]], ![[0, 1, 3], [1, 2, 3], [0, 1, 2], [0, 2, 3]], ![[3], [0], [2], [1]], ![[1], [2], [0], [3]], ![[0, 2, 3], [0, 1, 2], [1, 2, 3], [0, 1, 3]], ![[0, 1, 3], [0, 2, 3], [1, 2, 3], [0, 1, 2]], ![[3], [1], [0], [2]], ![[2], [3], [0], [1]], ![[0, 1, 2], [0, 1, 3], [1, 2, 3], [0, 2, 3]], ![[0, 2, 3], [0, 1, 3], [0, 1, 2], [1, 2, 3]], ![[1], [3], [2], [0]], ![[2], [1], [3], [0]], ![[0, 1, 2], [0, 2, 3], [0, 1, 3], [1, 2, 3]], ![[0, 1, 3], [0, 1, 2], [0, 2, 3], [1, 2, 3]], ![[3], [2], [1], [0]]]

theorem action_formula : ∀ (s : Fin 24) (v : BinaryFour) (i : Fin 4),
    (twistedAction (perm s) v).toAdd i = ((actionIndices s i).map v.toAdd).sum := by
  decide +kernel

def vectorValue (x : Fin 100 → ZMod 2) (v : Fin 4 → Poly) : BinaryFour :=
  Multiplicative.ofAdd (fun i => value x (v i))

set_option maxRecDepth 2048 in
theorem vectorValue_zero (x : Fin 100 → ZMod 2) : vectorValue x (fun _ => 0) = 1 := by
  apply Multiplicative.toAdd.injective
  simp only [vectorValue, toAdd_ofAdd, toAdd_one]
  exact funext (fun _ => value_zero x)

set_option maxRecDepth 2048 in
theorem vectorValue_xor (x : Fin 100 → ZMod 2) (v w : Fin 4 → Poly) :
    vectorValue x (fun i => v i ^^^ w i) = vectorValue x v * vectorValue x w := by
  apply Multiplicative.toAdd.injective
  funext i
  exact value_xor x (v i) (w i)

def polyAction (s : Fin 24) (v : Fin 4 → Poly) (i : Fin 4) : Poly :=
  sumPoly ((actionIndices s i).map v)

set_option maxRecDepth 2048 in
theorem vectorValue_action (x : Fin 100 → ZMod 2) (s : Fin 24) (v : Fin 4 → Poly) :
    vectorValue x (polyAction s v) = twistedAction (perm s) (vectorValue x v) := by
  apply Multiplicative.toAdd.injective
  funext i
  change value x (sumPoly ((actionIndices s i).map v)) = _
  rw [value_sumPoly, action_formula]
  simp only [List.map_map, Function.comp_def, vectorValue, toAdd_ofAdd]

def polyEdge (a : Fin 2) (t : Fin 24) (i : Fin 4) : Poly :=
  (slot a t i).elim 0 atom

set_option maxRecDepth 2048 in
theorem vectorValue_edge (x : Fin 100 → ZMod 2) (a : Fin 2) (t : Fin 24) :
    vectorValue x (polyEdge a t) = edge x a t := by
  apply Multiplicative.toAdd.injective
  funext i
  change value x ((slot a t i).elim 0 atom) = (slot a t i).elim 0 x
  cases slot a t i with
  | none => exact value_zero x
  | some k => exact value_atom x k

def polyExpand : List (Fin 2) → Fin 24 → Fin 4 → Poly
  | [], _, _ => 0
  | a :: w, t, i => polyEdge a (wordIndex w) i ^^^
      polyAction (gen a) (polyExpand w t) i ^^^ polyEdge a (mul (wordIndex w) t) i

theorem binary_inv_eq_self : ∀ v : BinaryFour, v⁻¹ = v := by decide +kernel

theorem vectorValue_expand (x : Fin 100 → ZMod 2) (w : List (Fin 2)) (t : Fin 24) :
    vectorValue x (polyExpand w t) = expand (edge x) w t := by
  induction w with
  | nil => exact vectorValue_zero x
  | cons a w ih =>
    change vectorValue x (fun i => (polyEdge a (wordIndex w) i ^^^
      polyAction (gen a) (polyExpand w t) i) ^^^ polyEdge a (mul (wordIndex w) t) i) = _
    rw [vectorValue_xor, vectorValue_xor, vectorValue_action, vectorValue_edge,
      vectorValue_edge, ih]
    simp only [expand, binary_inv_eq_self]

def polyTable (s t : Fin 24) : Fin 4 → Poly := polyExpand (words s) t

theorem vectorValue_table (x : Fin 100 → ZMod 2) (s t : Fin 24) :
    vectorValue x (polyTable s t) = table x s t := vectorValue_expand x (words s) t

def equation (s t u : Fin 24) (i : Fin 4) : Poly :=
  polyTable s t i ^^^ polyTable (mul s t) u i ^^^
    polyAction s (polyTable t u) i ^^^ polyTable s (mul t u) i

set_option maxRecDepth 2048 in
theorem equation_zero (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) (s t u : Fin 24) (i : Fin 4) :
    value x (equation s t u i) = 0 := by
  have hh := congrArg (fun v : BinaryFour => v.toAdd i) (h s t u)
  have ht : ∀ s t i, value x (polyTable s t i) = (table x s t).toAdd i :=
    fun s t i => congrArg (fun v : BinaryFour => v.toAdd i) (vectorValue_table x s t)
  have ha : value x (polyAction s (polyTable t u) i) =
      (twistedAction (perm s) (table x t u)).toAdd i := by
    have hv := vectorValue_action x s (polyTable t u)
    rw [vectorValue_table] at hv
    exact congrArg (fun v : BinaryFour => v.toAdd i) hv
  rw [equation, value_xor, value_xor, value_xor, ht, ht, ha, ht]
  change (table x s t).toAdd i + (table x (mul s t) u).toAdd i =
    (twistedAction (perm s) (table x t u)).toAdd i + (table x s (mul t u)).toAdd i at hh
  rw [add_assoc _ _ ((table x s (mul t u)).toAdd i), ← hh, CharTwo.add_self_eq_zero]

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions.TwistedCohomology
