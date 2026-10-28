module
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Four.Action
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Matrices of the actual coordinate-flag stabilizer

The SL-to-linear equivalence supplies the coordinate matrix of an actor.
Preservation of the initial coordinate spaces is equivalent to upper
triangularity, and invertibility over the binary field forces diagonal one.
The equivalence uses actual flag subspaces and actual linear maps.

Source: the standard upper-flag calculation used in the corrected
Aschbacher–Smith H.9.1(4), printed p.390.
-/

@[expose] public section

open BinaryNaturalDual BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.AdaptedPair.Four

/-- Matrix of an actor in the standard coordinate basis. -/
noncomputable def coordinateMatrix {n : ℕ} (g : LinearGroup n) :
    Matrix (Fin n) (Fin n) (ZMod 2) := ((slEquivLinear n).symm g).val

theorem coordinateMatrix_mulVec {n : ℕ} (g : LinearGroup n)
    (v : BinaryLinear.OuterCyclic.Space n) : (coordinateMatrix g).mulVec v = g v := by
  rw [coordinateMatrix, ← slEquivLinear_apply, MulEquiv.apply_symm_apply]

theorem coordinateMatrix_apply {n : ℕ} (g : LinearGroup n) (i j : Fin n) :
    coordinateMatrix g i j = g (axis j) i := by
  have h := congrFun (coordinateMatrix_mulVec g (Pi.single j 1)) i
  simpa only [axis, Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem coordinateMatrix_injective {n : ℕ} :
    Function.Injective (coordinateMatrix (n := n)) := by
  intro g h he
  apply (slEquivLinear n).symm.injective
  exact Subtype.ext he

theorem mem_upperGroup_iff_maps {n : ℕ} (g : LinearGroup n) :
    g ∈ upperGroup n ↔ ∀ k : Fin n, ∀ x ∈ initialSpace n (k.val + 1),
      g x ∈ initialSpace n (k.val + 1) := by
  rw [upperGroup, Subgroup.mem_iInf]
  constructor
  · intro h k x hx
    exact (h k x).mpr hx
  · intro h k x
    refine ⟨?_, h k x⟩
    intro hx
    let f : initialSpace n (k.val + 1) → initialSpace n (k.val + 1) :=
      fun y => ⟨g y, h k y y.property⟩
    have hf : Function.Injective f := by
      intro y z he
      exact Subtype.ext (g.injective (congrArg Subtype.val he))
    obtain ⟨y, hy⟩ := (Finite.surjective_of_injective hf) ⟨g x, hx⟩
    have hyx : (y : BinaryLinear.OuterCyclic.Space n) = x :=
      g.injective (congrArg Subtype.val hy)
    exact hyx ▸ y.property

/-- The flag definition is exactly upper triangularity. -/
theorem mem_upperGroup_iff {n : ℕ} (g : LinearGroup n) :
    g ∈ upperGroup n ↔ (coordinateMatrix g).IsUpperTriangular := by
  rw [mem_upperGroup_iff_maps]
  constructor
  · intro h i j hji
    rw [coordinateMatrix_apply]
    have hj : axis j ∈ initialSpace n (j.val + 1) :=
      Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩
    exact (mem_initialSpace_iff _).mp (h j _ hj) i
      (by change j.val < i.val at hji; omega)
  · intro h k v hv
    apply (mem_initialSpace_iff _).mpr
    intro i hi
    rw [← coordinateMatrix_mulVec]
    change ∑ j, coordinateMatrix g i j * v j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : k.val + 1 ≤ j.val
    · rw [(mem_initialSpace_iff _).mp hv j hj, mul_zero]
    · rw [h (show j < i from by change j.val < i.val; omega), zero_mul]

/-- Every diagonal entry of a binary upper invertible matrix is one. -/
theorem upper_diagonal {n : ℕ} {g : LinearGroup n} (hg : g ∈ upperGroup n)
    (i : Fin n) : coordinateMatrix g i i = 1 := by
  have hd : (coordinateMatrix g).det = 1 := ((slEquivLinear n).symm g).property
  rw [Matrix.det_of_isUpperTriangular ((mem_upperGroup_iff g).mp hg)] at hd
  have hp : (∏ j, coordinateMatrix g j j) ≠ 0 := by rw [hd]; exact one_ne_zero
  have hi := Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hi

end BinaryNaturalDual.AdaptedPair.Four
