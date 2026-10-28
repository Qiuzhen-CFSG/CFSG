module

public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.Charts

import all Theory.AlgebraicGroup.Instance.PGL2ProjectiveAction

/-!
# Infinity and the affine projective-line chart

The actual chart D(X_1) is the complement of the named point at infinity.
The proof uses homogeneous prime membership and proportional coordinate
vectors. This supplies the invariant affine chart in the projective-line
automorphism proof, without assuming a bijection of a replacement carrier.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
theorem projectivePoint_mem_chart (v : Fin 2 → k) (hv : v ≠ 0) (i : Fin 2) :
    (projectivePointOfVector v hv).val (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k i ↔
      v i ≠ 0 := by
  change MvPolynomial.X i ∉
    ((projectivePointOfVector v hv).val (IsLocalRing.closedPoint k)).asHomogeneousIdeal ↔ _
  rw [projectivePointOfVector_mem_iff v hv (coordinate_mem_p1Grading i)]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem point_mem_chart_one_iff_ne_infinity (x : Point (projectiveLine k)) :
    x.val (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k 1 ↔
      x ≠ projectiveLineInfinity := by
  obtain ⟨v,hv,rfl⟩ := point_vector_exists x
  rw [projectivePoint_mem_chart]
  constructor
  · intro h he
    have hm : (projectivePointOfVector v hv).val (IsLocalRing.closedPoint k) ∈
        projectiveLineChartOpen k 1 := (projectivePoint_mem_chart v hv 1).mpr h
    rw [he] at hm
    change (projectivePointOfVector projectiveLineInfinityVector _).val
      (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k 1 at hm
    rw [projectivePoint_mem_chart] at hm
    simp [projectiveLineInfinityVector] at hm
  · intro h he
    apply h
    change projectivePointOfVector v hv = projectivePointOfVector projectiveLineInfinityVector _
    rw [projectivePointOfVector_eq_iff_mk_eq]
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
    refine ⟨v 0,?_⟩
    funext j
    fin_cases j <;> simp [projectiveLineInfinityVector,he]

end
end Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
