module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.PointRealization.Clifford
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.CliffordCurves
import all Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.CliffordCurves

/-!
# The signed simple roots on the even half-spin coordinates

The Clifford formula `xᵣ(t) = 1 + t·uv` reduces the action on the sixteen
bit strings to creation and annihilation. On the eight even strings, in the
ordering of `HalfSpin.embedding`, these are precisely the natural orthogonal
root matrices with vertices permuted by `0 → 2 → 3 → 0`, fixing vertex `1`.
Both signs have the identical parameter `t`. The eight short coordinate
checks are separate declarations to bound elaboration cost.

This module continues the internal Clifford coordinate calculation of
`PinningTorus.RegularRoots.CliffordCurves`: the `import all` is intentional
and used only by the private `rootBivector_formula` bridge. The exported
identities mention only the public pinned points and natural root matrices.
No private implementation name becomes part of their public interface.

These are identities for the genuine representation of the fixed Clifford
Spin carrier, rather than a presentation on a separate group.
Source: GLS3, §§1.14.9(f) and 1.15.2(a).
-/

@[expose] public section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace Triality.SimplyConnected.Diagram.HalfSpin
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Pinning
variable (k : Type*) [Field k] [CharP k 2] [IsAlgClosed k]

private theorem rootBivector_formula (r : RootIndex) :
    rootBivector k r =
      CliffordAlgebra.ι (quadraticForm k)
        (if r.2.1.1 = 1 then (Pi.single r.1.1.1 1, 0) else (0, Pi.single r.1.1.1 1)) *
      CliffordAlgebra.ι (quadraticForm k)
        (if r.2.2.1 = 1 then (Pi.single r.1.1.2 1, 0) else (0, Pi.single r.1.1.2 1)) := rfl

private theorem positive_intertwines_0 (t : k) (v : QuadraticSpace k) :
    pointAction k (positiveSimplePoint k 0 t) (embedding k v) =
      embedding k ((evenOrthogonalRootQuadraticPoint 4
        (simpleRoot 2) t).val v) := by
  have hsign : (-1 : ℝ) ≠ 1 := by norm_num
  change cliffordAction k (pointEquiv k (rootPoint k (simpleRoot 0) t) :
    CliffordAlgebra (quadraticForm k)) (embedding k v) = _
  rw [rootPoint_clifford, map_add, map_one, map_smul]
  simp only [rootBivector_formula, map_mul, cliffordAction_ι]
  funext s
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  norm_num [negativeSimpleRoot, negativeRoot, simpleRoot, typeDSimpleRootIndex,
    vectorAction, Fin.sum_univ_four, Pi.single_apply]
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals
    simp [hsign, embedding, flip, h0, h1, h2, h3,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
      hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
      Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg]

private theorem positive_intertwines_1 (t : k) (v : QuadraticSpace k) :
    pointAction k (positiveSimplePoint k 1 t) (embedding k v) =
      embedding k ((evenOrthogonalRootQuadraticPoint 4
        (simpleRoot 1) t).val v) := by
  have hsign : (-1 : ℝ) ≠ 1 := by norm_num
  change cliffordAction k (pointEquiv k (rootPoint k (simpleRoot 1) t) :
    CliffordAlgebra (quadraticForm k)) (embedding k v) = _
  rw [rootPoint_clifford, map_add, map_one, map_smul]
  simp only [rootBivector_formula, map_mul, cliffordAction_ι]
  funext s
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  norm_num [negativeSimpleRoot, negativeRoot, simpleRoot, typeDSimpleRootIndex,
    vectorAction, Fin.sum_univ_four, Pi.single_apply]
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals
    simp [hsign, embedding, flip, h0, h1, h2, h3,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
      hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
      Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg]

private theorem positive_intertwines_2 (t : k) (v : QuadraticSpace k) :
    pointAction k (positiveSimplePoint k 2 t) (embedding k v) =
      embedding k ((evenOrthogonalRootQuadraticPoint 4
        (simpleRoot 3) t).val v) := by
  have hsign : (-1 : ℝ) ≠ 1 := by norm_num
  change cliffordAction k (pointEquiv k (rootPoint k (simpleRoot 2) t) :
    CliffordAlgebra (quadraticForm k)) (embedding k v) = _
  rw [rootPoint_clifford, map_add, map_one, map_smul]
  simp only [rootBivector_formula, map_mul, cliffordAction_ι]
  funext s
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  norm_num [negativeSimpleRoot, negativeRoot, simpleRoot, typeDSimpleRootIndex,
    vectorAction, Fin.sum_univ_four, Pi.single_apply]
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals
    simp [hsign, embedding, flip, h0, h1, h2, h3,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
      hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
      Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg]

private theorem positive_intertwines_3 (t : k) (v : QuadraticSpace k) :
    pointAction k (positiveSimplePoint k 3 t) (embedding k v) =
      embedding k ((evenOrthogonalRootQuadraticPoint 4
        (simpleRoot 0) t).val v) := by
  have hsign : (-1 : ℝ) ≠ 1 := by norm_num
  change cliffordAction k (pointEquiv k (rootPoint k (simpleRoot 3) t) :
    CliffordAlgebra (quadraticForm k)) (embedding k v) = _
  rw [rootPoint_clifford, map_add, map_one, map_smul]
  simp only [rootBivector_formula, map_mul, cliffordAction_ι]
  funext s
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  norm_num [negativeSimpleRoot, negativeRoot, simpleRoot, typeDSimpleRootIndex,
    vectorAction, Fin.sum_univ_four, Pi.single_apply]
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals
    simp [hsign, embedding, flip, h0, h1, h2, h3,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
      hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
      Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg]

private theorem negative_intertwines_0 (t : k) (v : QuadraticSpace k) :
    pointAction k (negativeSimplePoint k 0 t) (embedding k v) =
      embedding k ((evenOrthogonalRootQuadraticPoint 4
        (negativeSimpleRoot 2) t).val v) := by
  have hsign : (-1 : ℝ) ≠ 1 := by norm_num
  change cliffordAction k (pointEquiv k (rootPoint k (negativeSimpleRoot 0) t) :
    CliffordAlgebra (quadraticForm k)) (embedding k v) = _
  rw [rootPoint_clifford, map_add, map_one, map_smul]
  simp only [rootBivector_formula, map_mul, cliffordAction_ι]
  funext s
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  norm_num [negativeSimpleRoot, negativeRoot, simpleRoot, typeDSimpleRootIndex,
    vectorAction, Fin.sum_univ_four, Pi.single_apply]
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals
    simp [hsign, embedding, flip, h0, h1, h2, h3,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
      hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
      Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg]

private theorem negative_intertwines_1 (t : k) (v : QuadraticSpace k) :
    pointAction k (negativeSimplePoint k 1 t) (embedding k v) =
      embedding k ((evenOrthogonalRootQuadraticPoint 4
        (negativeSimpleRoot 1) t).val v) := by
  have hsign : (-1 : ℝ) ≠ 1 := by norm_num
  change cliffordAction k (pointEquiv k (rootPoint k (negativeSimpleRoot 1) t) :
    CliffordAlgebra (quadraticForm k)) (embedding k v) = _
  rw [rootPoint_clifford, map_add, map_one, map_smul]
  simp only [rootBivector_formula, map_mul, cliffordAction_ι]
  funext s
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  norm_num [negativeSimpleRoot, negativeRoot, simpleRoot, typeDSimpleRootIndex,
    vectorAction, Fin.sum_univ_four, Pi.single_apply]
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals
    simp [hsign, embedding, flip, h0, h1, h2, h3,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
      hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
      Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg]

private theorem negative_intertwines_2 (t : k) (v : QuadraticSpace k) :
    pointAction k (negativeSimplePoint k 2 t) (embedding k v) =
      embedding k ((evenOrthogonalRootQuadraticPoint 4
        (negativeSimpleRoot 3) t).val v) := by
  have hsign : (-1 : ℝ) ≠ 1 := by norm_num
  change cliffordAction k (pointEquiv k (rootPoint k (negativeSimpleRoot 2) t) :
    CliffordAlgebra (quadraticForm k)) (embedding k v) = _
  rw [rootPoint_clifford, map_add, map_one, map_smul]
  simp only [rootBivector_formula, map_mul, cliffordAction_ι]
  funext s
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  norm_num [negativeSimpleRoot, negativeRoot, simpleRoot, typeDSimpleRootIndex,
    vectorAction, Fin.sum_univ_four, Pi.single_apply]
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals
    simp [hsign, embedding, flip, h0, h1, h2, h3,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
      hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
      Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg]

private theorem negative_intertwines_3 (t : k) (v : QuadraticSpace k) :
    pointAction k (negativeSimplePoint k 3 t) (embedding k v) =
      embedding k ((evenOrthogonalRootQuadraticPoint 4
        (negativeSimpleRoot 0) t).val v) := by
  have hsign : (-1 : ℝ) ≠ 1 := by norm_num
  change cliffordAction k (pointEquiv k (rootPoint k (negativeSimpleRoot 3) t) :
    CliffordAlgebra (quadraticForm k)) (embedding k v) = _
  rw [rootPoint_clifford, map_add, map_one, map_smul]
  simp only [rootBivector_formula, map_mul, cliffordAction_ι]
  funext s
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  norm_num [negativeSimpleRoot, negativeRoot, simpleRoot, typeDSimpleRootIndex,
    vectorAction, Fin.sum_univ_four, Pi.single_apply]
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals
    simp [hsign, embedding, flip, h0, h1, h2, h3,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
      hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
      Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg]

/-- The half-spin action of each positive simple root, with unchanged parameter. -/
theorem positive_intertwines (i : Fin 4) (t : k) (v : QuadraticSpace k) :
    pointAction k (positiveSimplePoint k i t) (embedding k v) =
      embedding k ((evenOrthogonalRootQuadraticPoint 4
        (simpleRoot (typeD4DiagramPermutation i)) t).val v) := by
  fin_cases i
  · exact positive_intertwines_0 k t v
  · exact positive_intertwines_1 k t v
  · exact positive_intertwines_2 k t v
  · exact positive_intertwines_3 k t v

/-- The half-spin action of each negative simple root, with unchanged parameter. -/
theorem negative_intertwines (i : Fin 4) (t : k) (v : QuadraticSpace k) :
    pointAction k (negativeSimplePoint k i t) (embedding k v) =
      embedding k ((evenOrthogonalRootQuadraticPoint 4
        (negativeSimpleRoot (typeD4DiagramPermutation i)) t).val v) := by
  fin_cases i
  · exact negative_intertwines_0 k t v
  · exact negative_intertwines_1 k t v
  · exact negative_intertwines_2 k t v
  · exact negative_intertwines_3 k t v

end Triality.SimplyConnected.Diagram.HalfSpin
