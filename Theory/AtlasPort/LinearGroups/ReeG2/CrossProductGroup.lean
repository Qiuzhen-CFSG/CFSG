module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/CrossProductGroup.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.CrossProduct
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

theorem rowEquiv_mul (g h : Ambient F) (v : Vector F) :
    rowEquiv (g*h) v = rowEquiv h (rowEquiv g v) := by
  simp only [rowEquiv_apply, Units.val_mul, Matrix.vecMul_vecMul]

@[simp] theorem rowEquiv_one (v : Vector F) : rowEquiv (1 : Ambient F) v = v := by
  simp [rowEquiv_apply]

/-- The actual subgroup preserving the concrete alternating cross product. -/
def crossProductStabilizer : Subgroup (Ambient F) where
  carrier := {g | ∀ v w, crossProduct (rowEquiv g v) (rowEquiv g w) =
    rowEquiv g (crossProduct v w)}
  one_mem' := by intro v w; simp
  mul_mem' := by
    intro g h hg hh v w
    simp only [rowEquiv_mul]
    rw [hh (rowEquiv g v) (rowEquiv g w), hg v w]
  inv_mem' := by
    intro g hg v w
    have hc (x : Vector F) : rowEquiv g (rowEquiv g⁻¹ x) = x := by
      rw [← rowEquiv_mul,inv_mul_cancel,rowEquiv_one]
    apply (rowEquiv g).injective
    rw [← hg, hc, hc, hc]

theorem generated_preserves_crossProduct (m : ℕ) :
    generated F m ≤ crossProductStabilizer := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with (((⟨a,rfl⟩ | ⟨b,rfl⟩) | ⟨c,rfl⟩) | ⟨l,rfl⟩) | hw
  · exact alpha_preserves_crossProduct m a
  · exact beta_preserves_crossProduct m b
  · exact gamma_preserves_crossProduct m c
  · exact torus_preserves_crossProduct m l
  · have : g = upsilon := Set.mem_singleton_iff.mp hw
    subst g
    exact upsilon_preserves_crossProduct

/-- The exterior-kernel relations say exactly that the cross product vanishes. -/
theorem exteriorKernel_iff_crossProduct_zero (v w : Vector F) :
    exteriorKernel v w ↔ crossProduct v w = 0 := by
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6⟩
    ext i
    fin_cases i <;> simp only [crossProduct, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply]
    · linear_combination h0
    · linear_combination -h1
    · linear_combination h2
    · linear_combination h3
    · linear_combination h4
    · linear_combination -h5
    · linear_combination h6
  · intro h
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · have hi := congrFun h 0
      simp only [crossProduct, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Pi.zero_apply] at hi
      linear_combination hi
    · have hi := congrFun h 1
      simp only [crossProduct, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Pi.zero_apply] at hi
      linear_combination -hi
    · have hi := congrFun h 2
      simp only [crossProduct, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Pi.zero_apply] at hi
      linear_combination hi
    · have hi := congrFun h 3
      simp only [crossProduct, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Pi.zero_apply] at hi
      linear_combination hi
    · have hi := congrFun h 4
      simp only [crossProduct, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Pi.zero_apply] at hi
      linear_combination hi
    · have hi := congrFun h 5
      simp only [crossProduct, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Pi.zero_apply] at hi
      linear_combination -hi
    · have hi := congrFun h 6
      simp only [crossProduct, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Pi.zero_apply] at hi
      linear_combination hi

end Atlas.ReeG2

