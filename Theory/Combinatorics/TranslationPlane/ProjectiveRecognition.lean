module
public import Theory.Combinatorics.TranslationPlane.ProjectiveCompletion
public import Theory.Combinatorics.TranslationPlane.ProjectiveFieldChart
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Recognition from one-field affine line equations

The affine chart and its proved line equations construct an incidence
identification with the actual coordinate projective plane, including points
at infinity. The extension preserves the affine chart and the marked line.
This is the projective-coordinate step in the centerfree branch of DGS,
Groups and Graphs, 10.5 and Theorem D, printed pp.156,224.
-/

@[expose] public noncomputable section
namespace Configuration.TranslationPlane
variable {P L F : Type*} [Membership P L] [Finite P] [Finite L]
  [ProjectivePlane P L] [Field F] [Finite F]
variable (l : L) (c : (Fin 2 → F) ≃ {p : P // p ∉ l})
  (hl : ∀ m : L, m ≠ l → ∃ b v : Fin 2 → F, v ≠ 0 ∧
    ∀ t : Fin 2 → F, (c t).val ∈ m ↔ ∃ r : F, t = b + r • v)
include hl in
/-- A one-field affine line chart gives a literal incidence identification with PG(2,F). -/
theorem exists_projective_coordinates :
    ∃ (ep : P ≃ FieldChart.PG F) (el : L ≃ FieldChart.PG F),
      el l = FieldChart.axis F ∧ (∀ p m, ep p ∈ el m ↔ p ∈ m) ∧
      ∀ t : Fin 2 → F, ep (c t).val = FieldChart.point F t := by
  classical
  let e := c.symm.trans (FieldChart.chart F)
  have he : ∀ m : L, m ≠ l → ∃ m' : FieldChart.PG F, m' ≠ FieldChart.axis F ∧
      ∀ p : {p : P // p ∉ l}, (e p).val ∈ m' ↔ p.val ∈ m := by
    intro m hm
    obtain ⟨b,v,hv,h⟩ := hl m hm
    refine ⟨FieldChart.fieldLine F b v hv,FieldChart.fieldLine_ne_axis F b v hv,?_⟩
    intro p
    change FieldChart.point F (c.symm p) ∈ _ ↔ _
    rw [FieldChart.point_mem_fieldLine_iff, ←h (c.symm p),c.apply_symm_apply]
  obtain ⟨ep,el,hel,hi,ha⟩ := exists_incidence_extension l (FieldChart.axis F) e he (c 0)
  refine ⟨ep,el,hel,hi,?_⟩
  intro t
  rw [ha]
  change (FieldChart.chart F (c.symm (c t))).val = _
  rw [c.symm_apply_apply,FieldChart.chart_apply]
end Configuration.TranslationPlane
