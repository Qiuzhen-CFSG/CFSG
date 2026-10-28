module

public import CFSG.Quasithin.ChapterH.Section13To16.CodeLocal.CentralizerGeometry
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry.GroupStructure

/-!
# The Sylow-center application of the native group supplement

For a Sylow two-subgroup stabilizing an octad and a nonidentity generator of
its mapped center, the existing center-containment theorem supplies actual
pointwise-kernel membership. The affine construction then gives the native
supplement, conditional only on its two remaining affine-model calculations.

All subgroup inclusions, relative normality and intrinsic two-core maps are
retained in the published record. This does not yet assert H.16.2(6): the
model calculations and the subsequent identification with D must be proved.

Source: Aschbacher--Smith H.16.2(6), printed pp.402--403, citing Asc94, 39.1.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise

namespace CFSG.Quasithin.ChapterH.Section13To16
open MathieuCode.OctadAffine

/-- The actual Sylow-center application of the affine supplement construction.
The two explicit model calculations remain to be supplied; this is not an
unconditional assertion of H.16.2(6). -/
theorem code_sylow_center_supplement_of_affine
    (hcard : ∀ v : MathieuCode.OctadAffine.Space, v ≠ 0 → Nat.card (fiberKernel v) = 16)
    (hproduct : ∀ v : MathieuCode.OctadAffine.Space, v ≠ 0 →
      (translations : Set AffineGroup) * (fiberKernel v : Set AffineGroup) =
        ((pCore 2 (Subgroup.centralizer ({translation v} : Set AffineGroup))).map
          (Subgroup.centralizer ({translation v} : Set AffineGroup)).subtype : Set AffineGroup))
    (O : Octad) (T : Sylow 2 M24) (hT : (T : Subgroup M24) ≤ octadStabilizer O)
    (z : M24) (hne : z ≠ 1)
    (hz : Subgroup.zpowers z = (Subgroup.center T).map (T : Subgroup M24).subtype) :
    Nonempty (MathieuCode.OctadInvolutionSupplement O z) := by
  have hcenter : z ∈ (Subgroup.center T).map (T : Subgroup M24).subtype := by
    rw [← hz]
    exact Subgroup.mem_zpowers z
  have hkernel := code_sylow_center_mem_octadKernel O T hT z hcenter
  have hpointwise : z ∈ MathieuCode.octadPointwiseKernel O := by
    simpa only [octadKernel, MathieuCode.octad_core_map_eq_pointwise] using hkernel
  exact MathieuCode.octadInvolutionSupplement_of_affine hcard hproduct O z hpointwise hne

end CFSG.Quasithin.ChapterH.Section13To16
