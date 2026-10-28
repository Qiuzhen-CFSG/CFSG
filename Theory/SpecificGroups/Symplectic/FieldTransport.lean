module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Field.ZMod

/-!
# Field transport for symplectic groups of arbitrary rank

Apply a field isomorphism entrywise to the actual symplectic matrices, then
descend through their centers. The projection compatibility retains the
literal quotient map. In particular, a field of order two gives the same
projective carrier as `ZMod 2`, without recognizing groups from their orders.

Adapted from Gerald Höhn and the ATLAS contributors,
`Atlas/LinearGroups/Symplectic/FieldTransport.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`. Copyright (c) 2026.
Covered by the ATLAS Research and Attribution License 1.0; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
Changes: narrow CFSG module imports, literal Mathlib carriers, direct center
transport, and a prime-field comparison. The consumer is the binary branch
of the higher symplectic covering calculation in Aschbacher–Smith B.1.13.
-/

@[expose] public noncomputable section

namespace Theory.SpecificGroups.Symplectic

variable {r : ℕ} {F K : Type*} [Field F] [Field K]

/-- Entrywise transport of the actual symplectic matrix group in rank `r`. -/
def fieldEquivSp (e : F ≃+* K) :
    Matrix.symplecticGroup (Fin r) F ≃* Matrix.symplecticGroup (Fin r) K where
  toFun g := ⟨g.val.map e, SymplecticGroup.map_mem g.property e⟩
  invFun g := ⟨g.val.map e.symm, SymplecticGroup.map_mem g.property e.symm⟩
  left_inv g := by
    apply Subtype.ext
    ext i j
    exact e.symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    ext i j
    exact e.apply_symm_apply _
  map_mul' g h := by
    apply Subtype.ext
    exact Matrix.map_mul

@[simp] theorem fieldEquivSp_apply (e : F ≃+* K)
    (g : Matrix.symplecticGroup (Fin r) F) (i j : Fin r ⊕ Fin r) :
    (fieldEquivSp e g).val i j = e (g.val i j) := rfl

/-- Field transport descends through the full centers of the matrix groups. -/
def fieldEquivPSp (e : F ≃+* K) :
    (Matrix.symplecticGroup (Fin r) F ⧸ Subgroup.center (Matrix.symplecticGroup (Fin r) F)) ≃*
      (Matrix.symplecticGroup (Fin r) K ⧸ Subgroup.center (Matrix.symplecticGroup (Fin r) K)) :=
  QuotientGroup.congr _ _ (fieldEquivSp e) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro z
      obtain ⟨w, rfl⟩ := (fieldEquivSp e).surjective z
      simpa using congrArg (fieldEquivSp e) (Subgroup.mem_center_iff.mp hx w)
    · intro hy
      obtain ⟨x, rfl⟩ := (fieldEquivSp e).surjective y
      refine ⟨x, ?_, rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro w
      apply (fieldEquivSp e).injective
      simpa using Subgroup.mem_center_iff.mp hy (fieldEquivSp e w))

@[simp] theorem fieldEquivPSp_projection (e : F ≃+* K)
    (g : Matrix.symplecticGroup (Fin r) F) :
    fieldEquivPSp e (QuotientGroup.mk' _ g) =
      QuotientGroup.mk' _ (fieldEquivSp e g) := rfl

/-- An actual field isomorphism identifies every binary coefficient field. -/
def fieldEquivZModTwo (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2) : F ≃+* ZMod 2 := by
  letI : Fintype F := Fintype.ofFinite F
  exact (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [← Nat.card_eq_fintype_card] using hF)).symm

end Theory.SpecificGroups.Symplectic
