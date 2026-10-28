module

public import Theory.GroupTheory.DihedralCentralProductThree.Model
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.Geometry

/-!
# The two literal models of the threefold dihedral central product

Evaluation at the three coordinates identifies the finite function product
with the triple product used by fusion. It carries the two central overlap
relations to the two defining relations of that consumer, and hence descends
to a multiplicative equivalence of the exact quotient groups.
Source: Aschbacher–Smith 15.3.58(2), printed p.1149.
-/

@[expose] public section
open Subgroup DihedralGroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition
open DihedralCentralProductThree Cubic.HLocal

/-- Evaluation in the original order of the three dihedral factors. -/
def dihedralProductEquiv : D ≃* DihedralTriple where
  toFun x := (x 0, x 1, x 2)
  invFun x := ![x.1, x.2.1, x.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv x := rfl
  map_mul' x y := rfl

private theorem relation_zero : dihedralProductEquiv (relation 0) =
    ((r 2, r 2, 1) : DihedralTriple) := by decide

private theorem relation_one : dihedralProductEquiv (relation 1) =
    ((r 2, 1, r 2) : DihedralTriple) := by decide

/-- Both presentations impose precisely the same marked central overlaps. -/
theorem dihedralProductEquiv_relations :
    Delta.map dihedralProductEquiv.toMonoidHom = cubeRelations := by
  let : (Delta.map dihedralProductEquiv.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ dihedralProductEquiv.surjective
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro x ⟨i, rfl⟩
    change dihedralProductEquiv (relation i) ∈ cubeRelations
    fin_cases i
    · change dihedralProductEquiv (relation 0) ∈ cubeRelations
      rw [relation_zero]
      exact subset_normalClosure (by simp)
    · change dihedralProductEquiv (relation 1) ∈ cubeRelations
      rw [relation_one]
      exact subset_normalClosure (by simp)
  · apply normalClosure_le_normal
    rintro x (rfl | rfl)
    · exact ⟨relation 0, subset_closure ⟨0, rfl⟩, relation_zero⟩
    · exact ⟨relation 1, subset_closure ⟨1, rfl⟩, relation_one⟩

/-- The exact plus-type carrier consumed by the later fusion argument. -/
noncomputable def dihedralCubeEquiv : DihedralCentralProductThree.Model ≃* DihedralCube :=
  QuotientGroup.congr Delta cubeRelations dihedralProductEquiv dihedralProductEquiv_relations

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition
