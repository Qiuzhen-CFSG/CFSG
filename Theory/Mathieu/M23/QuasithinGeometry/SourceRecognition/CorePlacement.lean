module
public import Theory.Mathieu.M23.QuasithinGeometry.StandardSystem
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.KernelNormalizer
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Order
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Local
public import Theory.ElementaryAbelian.Injective

/-!
# Distinguishing the native heptad core inside the edge fixer

The elementary heptad kernel has order sixteen and lies in the native edge
fixer. It is not normalized by that whole edge fixer: otherwise both native
vertex and global generation identities put M23 in its proper heptad normalizer.
Thus it cannot be the characteristic two-core of the edge fixer.

Source: Aschbacher--Smith 5.2.20(5), printed p.656. The original-group application
uses this distinction to select the second full elementary Sylow plane.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace Sporadic.Mathieu.M23Geometry
open GraphUniquenessSystem

theorem heptadKernelAmbient_not_normalized_by_edge :
    ¬ standardSystem.edgeGroup ≤ normalizer (heptadKernelAmbient : Set M23) := by
  rw [heptadKernelAmbient_normalizer]
  intro h
  have hi : standardSystem.H ≤ heptadStabilizer := fourStabilizer_le
  have hv : standardSystem.vertexGroup ≤ heptadStabilizer := by
    change MulAction.stabilizer M23 standardSystem.x ≤ heptadStabilizer
    rw [←standardSystem.vertex_generate]
    exact sup_le h (inf_le_left.trans hi)
  have ht : heptadStabilizer = ⊤ := top_unique (standardSystem.generate ▸ sup_le hi hv)
  have hh := heptadStabilizer_index
  rw [ht,index_top] at hh
  norm_num at hh

theorem heptadKernelAmbient_elementary : IsElementaryAbelian 2 heptadKernelAmbient := by
  let : IsElementaryAbelian 2 heptadKernel := {
    toIsMulCommutative := IsMulCommutative.of_comm heptadKernel_mul_comm
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr heptadKernel_sq }
  exact IsElementaryAbelian.map _

end Sporadic.Mathieu.M23Geometry
