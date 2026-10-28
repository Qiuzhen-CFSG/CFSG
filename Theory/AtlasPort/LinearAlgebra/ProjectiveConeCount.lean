module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearAlgebra/ProjectiveConeCount.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! Affine fibres and projective scalar coordinates used to count singular vectors and points. -/

@[expose] public section

/-! Projectivizing a scalar-invariant cone removes one nonzero scalar parameter. -/
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.LinearAlgebra
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (P : V → Prop) (hP : ∀ (a : Fˣ) (v : V), P (a • v) ↔ P v)

abbrev ConePoints := {p : ℙ F V // P p.rep}
abbrev NonzeroCone := {v : V // v ≠ 0 ∧ P v}
include hP

theorem cone_mk_iff (v : V) (hv : v ≠ 0) :
    P (Projectivization.mk F v hv).rep ↔ P v := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
  rw [← ha]
  exact hP a v

def conePointMk (v : NonzeroCone P) : ConePoints (F := F) P :=
  ⟨Projectivization.mk F v.val v.prop.1, (cone_mk_iff P hP _ _).mpr v.prop.2⟩

def pointScalarVector (p : ConePoints (F := F) P × Fˣ) : NonzeroCone P :=
  ⟨p.2 • p.1.val.rep, by
    constructor
    · exact smul_ne_zero p.2.ne_zero p.1.val.rep_nonzero
    · exact (hP p.2 p.1.val.rep).mpr p.1.prop⟩

theorem conePointMk_pointScalarVector (p : ConePoints (F := F) P × Fˣ) :
    conePointMk P hP (pointScalarVector P hP p) = p.1 := by
  apply Subtype.ext
  change Projectivization.mk F (p.2 • p.1.val.rep) _ = p.1.val
  exact ((Projectivization.mk_eq_mk_iff F _ _ _ p.1.val.rep_nonzero).mpr
    ⟨p.2,rfl⟩).trans (Projectivization.mk_rep p.1.val)

theorem pointScalarVector_bijective :
    Function.Bijective (pointScalarVector P hP) := by
  constructor
  · rintro ⟨p,a⟩ ⟨q,b⟩ h
    have hp := congrArg (conePointMk P hP) h
    simp only [conePointMk_pointScalarVector] at hp
    change p = q at hp
    subst q
    have hv := congrArg Subtype.val h
    have hab : a = b := by
      apply Units.ext
      exact (smul_left_injective F p.val.rep_nonzero) hv
    subst b
    rfl
  · intro v
    let p := conePointMk P hP v
    obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F v.val v.prop.1
    refine ⟨(p,a⁻¹), ?_⟩
    apply Subtype.ext
    change a⁻¹ • (Projectivization.mk F v.val v.prop.1).rep = v.val
    rw [← ha, inv_smul_smul]

/-- Actual vectors are uniquely a marked projective representative times a unit. -/
def nonzeroConeEquivPointsUnits : NonzeroCone P ≃ ConePoints (F := F) P × Fˣ :=
  (Equiv.ofBijective (pointScalarVector P hP) (pointScalarVector_bijective P hP)).symm

theorem card_nonzeroCone :
    Nat.card (NonzeroCone P) = Nat.card (ConePoints (F := F) P) * (Nat.card F - 1) := by
  rw [Nat.card_congr (nonzeroConeEquivPointsUnits P hP), Nat.card_prod, Nat.card_units]

theorem card_conePoints [Finite F] :
    Nat.card (ConePoints (F := F) P) = Nat.card (NonzeroCone P) / (Nat.card F - 1) := by
  rw [card_nonzeroCone P hP, Nat.mul_div_cancel]
  have := Finite.one_lt_card (α := F)
  omega

end Atlas.LinearAlgebra
