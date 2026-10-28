module

public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.TriangleOrbit

/-!
# Aligning the exterior model with the F.5 vertex

A literal commutator of two isometries cycles the three standard negative
lines. It carries the sign change on the first two coordinates to the source
graph involution. This supplies both membership in the derived orthogonal
group and the involution marking used when extending its simple vertex group.

Source: Aschbacher–Smith F.5.1(1), F.5.3(6), printed pp.300–301.
-/

@[expose] public section
namespace OmegaSixThree
open SixTernaryCoordinates

/-- The isometry exchanging the first two standard negative vectors. -/
def switchFirstSecond : LinearGroup where
  toFun v := ![-v 0-v 1+v 5, -v 0-v 1-v 5, v 2, v 3, v 4, -v 0+v 1]
  invFun v := ![-v 0-v 1+v 5, -v 0-v 1-v 5, v 2, v 3, v 4, -v 0+v 1]
  left_inv v := by
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp [show (3 : ZMod 3) = 0 by decide, show (2 : ZMod 3) = -1 by decide]
  right_inv v := by
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp [show (3 : ZMod 3) = 0 by decide, show (2 : ZMod 3) = -1 by decide]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

theorem switchFirstSecond_orthogonal : switchFirstSecond ∈ orthogonalGroup := by
  intro v
  simp only [quadratic, switchFirstSecond, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring_nf
  simp [show (6 : ZMod 3) = 0 by decide, show (2 : ZMod 3) = -1 by decide, sub_eq_add_neg]

/-- The three-cycle x↦z↦y↦x, realized inside the derived isometry group. -/
def triangleCycle : omegaPlusSixThree :=
  ⟨commutatorWord switchFirstSecond (signChange {1}),
    commutatorWord_mem_omegaPlusSixThree switchFirstSecond_orthogonal
      (signChange_mem_orthogonalGroup {1})⟩

theorem triangleCycle_apply (v : Space) :
    triangleCycle.val v =
      ![-v 0-v 1+v 5, v 0+v 1+v 5, v 2, v 3, v 4, -v 0+v 1] := by
  ext i
  fin_cases i <;>
    simp [triangleCycle, commutatorWord, switchFirstSecond, LinearEquiv.mul_apply] <;>
    ring_nf <;>
    simp [show (2 : ZMod 3) = -1 by decide, sub_eq_add_neg]

/-- The cycle sends the exterior model's distinguished negative vector to e₅. -/
theorem triangleCycle_standard_vectors :
    triangleCycle.val (e 5) = e 0 + e 1 ∧
      triangleCycle.val (e 0-e 1) = e 5 ∧
      triangleCycle.val (e 0+e 1) = e 0-e 1 := by
  simp only [triangleCycle_apply]
  decide +kernel

theorem triangleCycle_conjugates_pairSignChange :
    triangleCycle.val * signChange {0,1} * triangleCycle.val⁻¹ = graphInvolution := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  ext v i
  fin_cases i <;> simp [LinearEquiv.mul_apply, triangleCycle_apply] <;> ring

/-- The source graph involution belongs to the actual derived orthogonal group. -/
theorem graphInvolution_mem_omegaPlusSixThree : graphInvolution ∈ omegaPlusSixThree := by
  rw [← triangleCycle_conjugates_pairSignChange]
  exact omegaPlusSixThree.mul_mem
    (omegaPlusSixThree.mul_mem triangleCycle.property pairSignChange_mem_omegaPlusSixThree)
    (omegaPlusSixThree.inv_mem triangleCycle.property)

/-- The literal source graph involution as an element of the model group. -/
def vertexGraphInvolution : omegaPlusSixThree :=
  ⟨graphInvolution, graphInvolution_mem_omegaPlusSixThree⟩

end OmegaSixThree
