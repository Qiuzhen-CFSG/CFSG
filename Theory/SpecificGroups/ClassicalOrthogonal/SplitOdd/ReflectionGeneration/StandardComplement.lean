/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.Complement

/-!
# The standard split complement

Adapted from the split-D portion of
`Atlas/LinearGroups/Orthogonal/StandardComplement.lean`. Removing the first
coordinate pair is an actual quadratic isometry with the split space of
rank one less. The inverse inserts two zero coordinates. Odd-dimensional
forms and their transitivity results are omitted; imports and namespaces
are adapted for CFSG / Lean 4.33.
-/

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup

namespace ClassicalOrthogonal.ReflectionGeneration
variable {n : ℕ} {F : Type u} [Field F]

def insertD (x : VectorD n F) : VectorD (n+1) F :=
  Sum.elim (Fin.cons 0 (fun i => x (.inl i))) (Fin.cons 0 (fun i => x (.inr i)))

def tailD (x : VectorD (n+1) F) : VectorD n F :=
  Sum.elim (fun i => x (.inl i.succ)) (fun i => x (.inr i.succ))

@[simp] theorem tail_insertD (x : VectorD n F) : tailD (insertD x) = x := by
  funext i
  cases i <;> rfl

@[simp] theorem form_insertD (x : VectorD n F) :
    formD (n+1) F (insertD x) = formD n F x := by
  simp [formD_apply, Fin.sum_univ_succ, insertD]

/-- Remove the first hyperbolic coordinate pair, retaining the quadratic form. -/
def standardComplementD :
    (ClassicalOrthogonal.Quadratic.complementForm (formD (n+1) F) (e 0) (f 0)).IsometryEquiv
      (formD n F) where
  toFun x := tailD x.val
  invFun x := ⟨insertD x, by
    simp only [ClassicalOrthogonal.Quadratic.mem_complement, polarD_e, polarD_f]
    exact ⟨rfl, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.prop
    change (formD (n+1) F).polarBilin x.val (e 0) = 0 ∧
      (formD (n+1) F).polarBilin x.val (f 0) = 0 at hx
    simp only [polarD_e, polarD_f] at hx
    funext i
    cases i with
    | inl j =>
      refine Fin.cases ?_ (fun k => rfl) j
      exact hx.2.symm
    | inr j =>
      refine Fin.cases ?_ (fun k => rfl) j
      exact hx.1.symm
  right_inv := tail_insertD
  map_add' x y := by funext i; cases i <;> rfl
  map_smul' a x := by funext i; cases i <;> rfl
  map_app' x := by
    have hx := x.prop
    change (formD (n+1) F).polarBilin x.val (e 0) = 0 ∧
      (formD (n+1) F).polarBilin x.val (f 0) = 0 at hx
    simp only [polarD_e, polarD_f] at hx
    change formD n F (tailD x.val) = formD (n+1) F x.val
    simp [formD_apply, Fin.sum_univ_succ, hx.1, hx.2, tailD]



end ClassicalOrthogonal.ReflectionGeneration
