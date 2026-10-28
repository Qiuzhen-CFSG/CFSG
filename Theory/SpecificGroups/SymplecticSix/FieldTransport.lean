module

public import Theory.SpecificGroups.SymplecticSix.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Field transport for the binary rank-three symplectic carrier

The local rank and two-core calculations for `PSp₆(2)` are separate from this
module.  This file records the exact carrier transport needed by those
calculations: applying a field isomorphism entrywise gives an equivalence of
the full symplectic matrix groups and hence of their central quotients.  In
particular, every field of cardinality two can be transported to `ZMod 2`
without identifying groups merely from their orders.

The entrywise construction is adapted from
`Atlas/LinearGroups/Symplectic/FieldTransport.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, under the ATLAS Research and
Attribution License 1.0. Copyright (c) 2026 Gerald Höhn and the ATLAS
contributors. All rights reserved. See `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`. Changes: specialize to the six-space CFSG
carrier, prove preservation of the center directly, and add binary transport.
-/

@[expose] public section
noncomputable section

namespace Theory.SpecificGroups.SymplecticSix

variable {F K : Type*} [Field F] [Field K]

/-- Entrywise transport of the actual full matrix group. -/
def fieldEquivSp (e : F ≃+* K) : Sp F ≃* Sp K where
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

@[simp] theorem fieldEquivSp_apply (e : F ≃+* K) (g : Sp F)
    (i j : Fin 3 ⊕ Fin 3) : (fieldEquivSp e g).val i j = e (g.val i j) := rfl

/-- Transport of the central quotient, retaining the actual projective carrier. -/
def fieldEquivPSp (e : F ≃+* K) : PSp F ≃* PSp K :=
  QuotientGroup.congr _ _ (fieldEquivSp e) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro z
      obtain ⟨w, rfl⟩ := (fieldEquivSp e).surjective z
      have hc := Subgroup.mem_center_iff.mp hx w
      simpa using congrArg (fieldEquivSp e) hc
    · intro hy
      obtain ⟨x, rfl⟩ := (fieldEquivSp e).surjective y
      refine ⟨x, ?_, rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro w
      have hc := Subgroup.mem_center_iff.mp hy (fieldEquivSp e w)
      apply (fieldEquivSp e).injective
      simpa using hc)

@[simp] theorem fieldEquivPSp_projection (e : F ≃+* K) (g : Sp F) :
    fieldEquivPSp e (QuotientGroup.mk' (Subgroup.center (Sp F)) g) =
      QuotientGroup.mk' (Subgroup.center (Sp K)) (fieldEquivSp e g) := rfl

/-- The unique field model used for the binary rank-three carrier. -/
def fieldEquivZModTwo (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2) : F ≃+* ZMod 2 := by
  letI : Fintype F := Fintype.ofFinite F
  exact (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [← Nat.card_eq_fintype_card] using hF)).symm

/-- Transport of the actual `PSp₆` carrier to the binary prime field. -/
def pspFieldEquivZModTwo (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2) : PSp F ≃* PSp (ZMod 2) :=
  fieldEquivPSp (fieldEquivZModTwo F hF)


end Theory.SpecificGroups.SymplecticSix
