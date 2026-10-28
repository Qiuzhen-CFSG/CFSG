module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.Bounds
public import Theory.GroupTheory.CosetWordCertificate
import Mathlib.Tactic.FinCases

/-!
# Word certificates for the O'Nan coset upper bound

The four letters represent the two ambient generators and the two specified
local subgroup words. Subgroup loops use only the last two letters. A word
whose linear evaluation is scalar is a genuine projective relator; no claim
that the relators present O'Nan's group is needed for a coset upper bound.

Source matrices and subgroup words: `refs/original/onan/` and
`ProjectiveOrder/source/`. Coset-trace soundness is in
`Theory.GroupTheory.CosetWordCertificate`.
-/

namespace ONan.OrderCertificate.UpperBound

open Subgroup.CosetWordCertificate

/-- Ambient letters followed by the two local subgroup words. -/
@[expose] public def generators : Fin 4 → Model :=
  ![generatorA, generatorB, localA, localB]

/-- The same words evaluated in the published linear lifts. -/
@[expose] public def linearGenerators : Fin 4 →
    Matrix.GeneralLinearGroup (Fin 45) (ZMod 7) :=
  ![linearA, linearB, linearB⁻¹ * linearA * linearB,
    ((linearA * linearB ^ 2) ^ 2)⁻¹ * linearB * (linearA * linearB ^ 2) ^ 2]

/-- The two letters allowed to create subgroup loops. -/
@[expose] public def allowed (a : Letter (Fin 4)) : Bool :=
  a.1 == 2 || a.1 == 3

public theorem project_linearGenerators (i : Fin 4) :
    Matrix.ProjGenLinGroup.mk (linearGenerators i) = (generators i).val := by
  fin_cases i <;>
    simp [linearGenerators, generators, localA, localB, generatorA, generatorB,
      projectiveA, projectiveB, map_mul, map_inv, map_pow] <;> rfl

public theorem project_eval (w : Word (Fin 4)) :
    Matrix.ProjGenLinGroup.mk (eval linearGenerators w) = (eval generators w).val := by
  induction w with
  | nil => simp; rfl
  | cons a w ih =>
    rw [eval_cons, eval_cons]
    cases a with
    | mk i sign =>
      cases sign <;> simp [map_mul, map_inv, project_linearGenerators, ih] <;> rfl

/-- A full linear word equality to a scalar gives a projective relator. -/
public theorem relator_of_scalar (w : Word (Fin 4)) (u : (ZMod 7)ˣ)
    (h : eval linearGenerators w = Matrix.GeneralLinearGroup.scalar (Fin 45) u) :
    eval generators w = 1 := by
  apply Subtype.ext
  rw [← project_eval, h, Matrix.ProjGenLinGroup.mk_scalar]
  rfl

/-- Both signs of either local letter evaluate in the specified subgroup. -/
public theorem allowed_mem (a : Letter (Fin 4)) (h : allowed a = true) :
    eval generators [a] ∈ localSubgroup := by
  have hi : a.1 = 2 ∨ a.1 = 3 := by simpa [allowed] using h
  rw [eval_letter]
  have hm : generators a.1 ∈ localSubgroup := by
    rcases hi with hi | hi
    · simpa [hi, generators] using localA_mem
    · simpa [hi, generators] using localB_mem
  split
  · exact hm
  · exact localSubgroup.inv_mem hm

/-- Every signed word in the local letters remains in the local subgroup. -/
public theorem eval_mem_of_allowed (w : Word (Fin 4))
    (h : ∀ a ∈ w, allowed a = true) : eval generators w ∈ localSubgroup := by
  induction w with
  | nil => simp only [eval_nil]; exact localSubgroup.one_mem
  | cons a w ih =>
    change eval generators ([a] ++ w) ∈ localSubgroup
    rw [eval_append]
    exact localSubgroup.mul_mem (allowed_mem a (h a (List.mem_cons_self ..)))
      (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- A full 45-dimensional equality up to scalar certifies a coset transition.
The factor word uses only the specified local letters, in either sign. -/
public theorem step_of_scalar (left right factor : Word (Fin 4)) (a : Fin 4)
    (hf : ∀ b ∈ factor, allowed b = true) (u : (ZMod 7)ˣ)
    (he : (eval linearGenerators left * linearGenerators a) *
        Matrix.GeneralLinearGroup.scalar (Fin 45) u =
      eval linearGenerators factor * eval linearGenerators right) :
    ∃ h : localSubgroup,
      eval generators left * generators a = h.val * eval generators right := by
  refine ⟨⟨eval generators factor, eval_mem_of_allowed factor hf⟩, ?_⟩
  apply Subtype.ext
  change (eval generators left).val * (generators a).val =
    (eval generators factor).val * (eval generators right).val
  have hp := congrArg Matrix.ProjGenLinGroup.mk he
  simpa only [map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one,
    project_eval, project_linearGenerators] using hp

/-- A cover for all four letters restricts to the two ambient generators. -/
public def restrictCover
    (C : Subgroup.GeneratorCosetCover localSubgroup generators (Fin 122760)) :
    Subgroup.GeneratorCosetCover localSubgroup cosetGenerators (Fin 122760) where
  repr := C.repr
  initial := C.initial
  initial_eq := C.initial_eq
  step i a := by
    cases a
    · exact C.step i 0
    · exact C.step i 1
  inv_step i a := by
    cases a
    · exact C.inv_step i 0
    · exact C.inv_step i 1

/-- Instantiate a trace context from proved relators and its defining tree. -/
public theorem valid (D : Definitions (Fin 4)) (rels : Nat → Word (Fin 4))
    (hr : ∀ r, eval generators (rels r) = 1) :
    Valid ⟨D.parent, D.letter, rels, allowed⟩ localSubgroup generators
      (D.repr generators) :=
  D.valid rels allowed allowed_mem hr

end ONan.OrderCertificate.UpperBound
