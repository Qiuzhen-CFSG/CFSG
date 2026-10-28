module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Roots
/-!
# Highest-root centralization in the concrete Spin group

Every positive D4 root group commutes with the highest-root group.
The calculation uses two elementary identities on the eight-dimensional
hyperbolic space and lifts through the faithful Spin action. It supplies
exactly the central highest-vector input for the rational adjoint module.

Source: GLS3 §1.12 and Example 1.14.9(c).
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.Standard.PositiveCoordinates
namespace Triality.SimplyConnected.Pinning
universe u
variable (k : Type u) [Field k]

private theorem upper_highest (i j : Fin 4) (hij : i < j) (a b : k) :
    Commute (hyperbolicUpperRootLinearEquiv 4 i j hij.ne a)
      (hyperbolicSkewUpperRootLinearEquiv 4 0 1 (by decide) b) := by
  change _ * _ = _ * _
  apply LinearEquiv.ext
  intro v
  apply Prod.ext <;> funext p
  all_goals
    have hj0 : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hij)
    by_cases hj1 : j = 1
  all_goals
    try have hi : i = 0 := by omega
  all_goals
    simp_all [hyperbolicUpperRootLinearEquiv, hyperbolicSkewUpperRootLinearEquiv,
      Pi.single_apply]
  all_goals split_ifs <;> simp_all <;> ring

private theorem skew_highest (i j : Fin 4) (hij : i ≠ j) (a b : k) :
    Commute (hyperbolicSkewUpperRootLinearEquiv 4 i j hij a)
      (hyperbolicSkewUpperRootLinearEquiv 4 0 1 (by decide) b) := by
  change _ * _ = _ * _
  apply LinearEquiv.ext
  intro v
  apply Prod.ext <;> funext p
  · simp [hyperbolicSkewUpperRootLinearEquiv]
    ring
  · rfl

private theorem matrix_commute (i : Fin 12) (a b : k) :
    Commute (evenOrthogonalRootQuadraticPoint 4 (rootIndex i) a)
      (evenOrthogonalRootQuadraticPoint 4 (rootIndex 11) b) := by
  change _ * _ = _ * _
  apply Subtype.ext
  change (evenOrthogonalRootIsometry 4 (rootIndex i) a).toLinearEquiv *
      (evenOrthogonalRootIsometry 4 (rootIndex 11) b).toLinearEquiv =
    (evenOrthogonalRootIsometry 4 (rootIndex 11) b).toLinearEquiv *
      (evenOrthogonalRootIsometry 4 (rootIndex i) a).toLinearEquiv
  rw [show rootIndex 11 = sumRoot 0 1 (by decide) from rfl]
  fin_cases i
  · norm_num only [rootIndex, Matrix.cons_val_zero', Matrix.cons_val_succ',
      difference, sumRoot, evenOrthogonalRootIsometry, reduceDIte]
    exact upper_highest k 0 1 (by decide) _ _
  · norm_num only [rootIndex, Matrix.cons_val_zero', Matrix.cons_val_succ',
      difference, sumRoot, evenOrthogonalRootIsometry, reduceDIte]
    exact upper_highest k 2 3 (by decide) _ _
  · norm_num only [rootIndex, Matrix.cons_val_zero', Matrix.cons_val_succ',
      difference, sumRoot, evenOrthogonalRootIsometry, reduceDIte]
    exact skew_highest k 2 3 (by decide) _ _
  · norm_num only [rootIndex, Matrix.cons_val_zero', Matrix.cons_val_succ',
      difference, sumRoot, evenOrthogonalRootIsometry, reduceDIte]
    exact upper_highest k 1 2 (by decide) _ _
  · norm_num only [rootIndex, Matrix.cons_val_zero', Matrix.cons_val_succ',
      difference, sumRoot, evenOrthogonalRootIsometry, reduceDIte]
    exact upper_highest k 0 2 (by decide) _ _
  · norm_num only [rootIndex, Matrix.cons_val_zero', Matrix.cons_val_succ',
      difference, sumRoot, evenOrthogonalRootIsometry, reduceDIte]
    exact upper_highest k 1 3 (by decide) _ _
  · norm_num only [rootIndex, Matrix.cons_val_zero', Matrix.cons_val_succ',
      difference, sumRoot, evenOrthogonalRootIsometry, reduceDIte]
    exact skew_highest k 1 3 (by decide) _ _
  · norm_num only [rootIndex, Matrix.cons_val_zero', Matrix.cons_val_succ',
      difference, sumRoot, evenOrthogonalRootIsometry, reduceDIte]
    exact upper_highest k 0 3 (by decide) _ _
  · norm_num only [rootIndex, Matrix.cons_val_zero', Matrix.cons_val_succ',
      difference, sumRoot, evenOrthogonalRootIsometry, reduceDIte]
    exact skew_highest k 1 2 (by decide) _ _
  · norm_num only [rootIndex, Matrix.cons_val_zero', Matrix.cons_val_succ',
      difference, sumRoot, evenOrthogonalRootIsometry, reduceDIte]
    exact skew_highest k 0 3 (by decide) _ _
  · norm_num only [rootIndex, Matrix.cons_val_zero', Matrix.cons_val_succ',
      difference, sumRoot, evenOrthogonalRootIsometry, reduceDIte]
    exact skew_highest k 0 2 (by decide) _ _
  · norm_num only [rootIndex, Matrix.cons_val_zero', Matrix.cons_val_succ',
      difference, sumRoot, evenOrthogonalRootIsometry, reduceDIte]
    exact skew_highest k 0 1 (by decide) _ _

variable [IsAlgClosed k] [CharP k 2]

theorem positive_rootPoint_commute_highest (r : RootIndex)
    (hr : (typeDRootPairing_base 2).IsPos r) (a b : k) :
    Commute (rootPoint k r a) (rootPoint k (rootIndex 11) b) := by
  obtain ⟨i, rfl⟩ := (Set.ext_iff.mp range_rootIndex r).mpr hr
  change _ * _ = _ * _
  apply naturalAction_injective k
  simp only [map_mul, naturalAction_rootPoint]
  exact matrix_commute k i a b

end Triality.SimplyConnected.Pinning
