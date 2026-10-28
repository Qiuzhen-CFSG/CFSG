module

public import Theory.LinearAlgebra.BinaryPointMap
public import Theory.LinearAlgebra.BinaryPolarity.Evaluation

/-!
# A binary polar geometry reconstructs its symplectic space

For a reflexive symmetric relation, take the binary row of non-incidence at
each point. The one-or-all rule on each three-point line says that two rows
sum to the third. If every point has a nonincident point, the row labels are
therefore precisely the nonzero vectors in their span. Evaluation at the
label of a nonzero vector defines a nondegenerate alternating form. This
keeps the original relation as literal orthogonality.

This is the linear reconstruction in Aschbacher–Smith I.5.15, printed p.424.
The row-span construction is the faithful image of the source permutation
module under its incidence form; it avoids choosing a presentation of the
relation quotient.
-/

@[expose] public noncomputable section
attribute [local instance] Classical.propDecidable
namespace Theory.LinearAlgebra.BinaryPolarGeometry
variable {X : Type*}

/-- Each point is related to either one or all three specified points. -/
def OneOrAll (R : X → X → Prop) (x y z : X) : Prop :=
  ∀ w, (R w x ∧ R w y ∧ R w z) ∨
    (R w x ∧ ¬ R w y ∧ ¬ R w z) ∨
    (¬ R w x ∧ R w y ∧ ¬ R w z) ∨
    (¬ R w x ∧ ¬ R w y ∧ R w z)

/-- The earlier incidence conclusions used by symplectic reconstruction. -/
structure Data (R : X → X → Prop) : Prop where
  reflexive : ∀ x, R x x
  symmetric : ∀ {x y}, R x y → R y x
  nonincident : ∀ x, ∃ y, ¬ R x y
  triples : ∀ x y, x ≠ y → ∃ z, OneOrAll R x y z

variable (R : X → X → Prop)
def row (x : X) : X → ZMod 2 := fun y => if R x y then 0 else 1
def rowSpan : Submodule (ZMod 2) (X → ZMod 2) :=
  Submodule.span _ (Set.range (row R))
abbrev Space := rowSpan R
def point (x : X) : Space R := ⟨row R x, Submodule.subset_span ⟨x, rfl⟩⟩

namespace Data
variable {R} (d : Data R)
include d in
theorem row_symmetric (x y : X) : row R x y = row R y x := by
  classical
  have h : R x y ↔ R y x := ⟨d.symmetric, d.symmetric⟩
  simp only [row, h]

include d in
theorem point_nonzero (x : X) : point R x ≠ 0 := by
  classical
  obtain ⟨y, hy⟩ := d.nonincident x
  intro h
  have he := congrArg (fun v : Space R => v.val y) h
  simp [point, row, hy] at he

include d in
theorem point_add (x y : X) (hxy : x ≠ y) :
    ∃ z, point R x + point R y = point R z := by
  classical
  obtain ⟨z, hz⟩ := d.triples x y hxy
  refine ⟨z, Subtype.ext (funext fun w => ?_)⟩
  change row R x w + row R y w = row R z w
  rw [d.row_symmetric x w, d.row_symmetric y w, d.row_symmetric z w]
  rcases hz w with h | h | h | h <;>
    simp [row, h.1, h.2.1, h.2.2, show (1 : ZMod 2) + 1 = 0 from rfl]

theorem span_points : Submodule.span (ZMod 2) (Set.range (point R)) = ⊤ := by
  exact (Submodule.span_range_subtype_eq_top_iff (rowSpan R)
    (fun x => Submodule.subset_span ⟨x, rfl⟩)).mpr rfl

include d in
theorem point_injective : Function.Injective (point R) :=
  BinaryPointMap.injective _ d.point_nonzero d.point_add

def pointEquiv : X ≃ {v : Space R // v ≠ 0} :=
  Equiv.ofBijective (fun x => ⟨point R x, d.point_nonzero x⟩)
    (BinaryPointMap.bijective_nonzero _ d.point_nonzero d.point_add (span_points (R := R)))

@[simp] theorem pointEquiv_apply (x : X) : (d.pointEquiv x).val = point R x := rfl

theorem point_label (v : {v : Space R // v ≠ 0}) :
    point R (d.pointEquiv.symm v) = v.val :=
  congrArg Subtype.val (d.pointEquiv.apply_symm_apply v)

def evaluation (x : X) : Space R →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj x).comp (rowSpan R).subtype

def functional (v : {v : Space R // v ≠ 0}) : Space R →ₗ[ZMod 2] ZMod 2 :=
  evaluation (R := R) (d.pointEquiv.symm v)

theorem functional_symmetric (v w : {v : Space R // v ≠ 0}) :
    d.functional v w = 0 ↔ d.functional w v = 0 := by
  have he : d.functional v w = d.functional w v := by
    change w.val.val (d.pointEquiv.symm v) = v.val.val (d.pointEquiv.symm w)
    rw [← d.point_label w, ← d.point_label v]
    exact d.row_symmetric _ _
  rw [he]

def form : LinearMap.BilinForm (ZMod 2) (Space R) :=
  BinaryPolarity.form d.functional d.functional_symmetric

theorem form_point (x : X) (v : Space R) : d.form (point R x) v = v.val x := by
  change BinaryPolarity.form d.functional d.functional_symmetric (point R x) v = _
  rw [BinaryPolarity.form_apply_nonzero _ _ (d.point_nonzero x)]
  change v.val (d.pointEquiv.symm (d.pointEquiv x)) = _
  rw [Equiv.symm_apply_apply]

theorem form_points (x y : X) : d.form (point R x) (point R y) = row R y x :=
  d.form_point x _

theorem orthogonal_iff (x y : X) : d.form (point R x) (point R y) = 0 ↔ R x y := by
  classical
  rw [d.form_points, d.row_symmetric y x]
  simp only [row, ite_eq_left_iff, one_ne_zero, imp_false, not_not]

theorem form_alternating : d.form.IsAlt := by
  apply BinaryPolarity.form_alternating
  intro v
  change v.val.val (d.pointEquiv.symm v) = 0
  rw [← d.point_label v]
  simp [point, row, d.reflexive]

theorem form_nondegenerate : d.form.Nondegenerate := by
  apply BinaryPolarity.form_nondegenerate
  intro v hv
  obtain ⟨y, hy⟩ := d.nonincident (d.pointEquiv.symm v)
  have he := LinearMap.congr_fun hv (point R y)
  change row R y (d.pointEquiv.symm v) = 0 at he
  rw [d.row_symmetric] at he
  simp [row, hy] at he

include d in
theorem space_finrank [Finite X] (n : ℕ) (hc : Nat.card X + 1 = 2 ^ n) :
    Module.finrank (ZMod 2) (Space R) = n :=
  BinaryPointMap.finrank _ d.point_nonzero d.point_add (span_points (R := R)) n hc

end Data
end Theory.LinearAlgebra.BinaryPolarGeometry
