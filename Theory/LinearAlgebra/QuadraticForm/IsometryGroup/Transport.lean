module

public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup

/-!
# Transport of full quadratic isometry groups

An isometry of quadratic spaces conjugates their full linear isometry groups.
The inverse conjugation and pointwise formulas retain the actual actions;
this applies in characteristic two without replacing the quadratic form by
its polar form.
-/

public section

namespace QuadraticMap.IsometryEquiv
variable {R V W : Type*} [CommRing R] [AddCommGroup V] [AddCommGroup W]
  [Module R V] [Module R W] {q : QuadraticForm R V} {q' : QuadraticForm R W}

/-- Conjugate the full linear isometry subgroup along an isometry of spaces. -/
def isometrySubgroupCongr (e : q.IsometryEquiv q') :
    q.isometrySubgroup ≃* q'.isometrySubgroup where
  toFun g := ⟨(e.toLinearEquiv.symm.trans g.val).trans e.toLinearEquiv, by
    apply (mem_isometrySubgroup q' _).mpr
    intro v
    change q' (e (g.val (e.symm v))) = q' v
    rw [e.map_app, (mem_isometrySubgroup q _).mp g.property, e.symm.map_app]⟩
  invFun g := ⟨(e.toLinearEquiv.trans g.val).trans e.toLinearEquiv.symm, by
    apply (mem_isometrySubgroup q _).mpr
    intro v
    change q (e.symm (g.val (e v))) = q v
    rw [e.symm.map_app, (mem_isometrySubgroup q' _).mp g.property, e.map_app]⟩
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change e.symm (e (g.val (e.symm (e v)))) = g.val v
    simp only [symm_apply_apply]
  right_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change e (e.symm (g.val (e (e.symm v)))) = g.val v
    simp only [apply_symm_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change e (g.val (h.val (e.symm v))) =
      e (g.val (e.symm (e (h.val (e.symm v)))))
    rw [symm_apply_apply]

@[simp] theorem isometrySubgroupCongr_apply (e : q.IsometryEquiv q')
    (g : q.isometrySubgroup) (v : W) :
    (e.isometrySubgroupCongr g).val v = e (g.val (e.symm v)) := by rfl

@[simp] theorem isometrySubgroupCongr_symm_apply (e : q.IsometryEquiv q')
    (g : q'.isometrySubgroup) (v : V) :
    (e.isometrySubgroupCongr.symm g).val v = e.symm (g.val (e v)) := by rfl

theorem isometrySubgroupCongr_intertwines (e : q.IsometryEquiv q')
    (g : q.isometrySubgroup) (v : V) :
    (e.isometrySubgroupCongr g).val (e v) = e (g.val v) := by
  rw [isometrySubgroupCongr_apply, symm_apply_apply]
end QuadraticMap.IsometryEquiv
