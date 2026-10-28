module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.MiddleCore.Images
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.MiddleCore.Coordinates

/-!
# Middle residual-flag radicals for the binary SL₅ exterior-square parabolics

The independent middle residual calculation identifies the terminal derived
subgroups with the kernels of the small SL₂ blocks. Conditional only on those
equalities, this module identifies the source radicals O₂(LᵢT), the genuine
flag quotients, and the images of the actual residuals. Every quotient map
retains the literal three-dimensional diagonal block. Quotients of residuals
use their intersections with the radicals; no containment Rᵢ ≤ Lᵢ is imposed.

The group calculations themselves are unconditional in the descendant modules.
The residual equalities remain with the source-theorem assembly owner.

Source: Aschbacher–Smith, Lemma 12.5.2(1–2), printed p.817/PDF p.834.
-/

@[expose] public section
open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare.MiddleCore
open SL5TenDimensional

/-- Apply the radical calculation to the actual source group L₁T. -/
theorem parabolicResidualTwoCore_two
    (h : parabolicResidual 2 = parabolicTwoLargeBlock) :
    parabolicResidualTwoCore 2 = twoRadical := by
  rw [parabolicResidualTwoCore, parabolicResidualFlag, h]
  exact twoCore_map

/-- Apply the radical calculation to the actual source group L₃T. -/
theorem parabolicResidualTwoCore_three
    (h : parabolicResidual 3 = parabolicThreeLargeBlock) :
    parabolicResidualTwoCore 3 = threeRadical := by
  rw [parabolicResidualTwoCore, parabolicResidualFlag, h]
  exact threeCore_map

private theorem source_twoFlag_eq (h : parabolicResidual 2 = parabolicTwoLargeBlock) :
    parabolicResidualFlag 2 = twoFlag := by rw [parabolicResidualFlag, h]; rfl

private theorem source_threeFlag_eq (h : parabolicResidual 3 = parabolicThreeLargeBlock) :
    parabolicResidualFlag 3 = threeFlag := by rw [parabolicResidualFlag, h]; rfl

/-- The marked quotient of the actual source overgroup, once its residual is identified. -/
noncomputable def sourceTwoFlagQuotientEquiv
    (h : parabolicResidual 2 = parabolicTwoLargeBlock) :
    (parabolicResidualFlag 2 ⧸ pCore 2 (parabolicResidualFlag 2)) ≃* SL(3, ZMod 2) :=
  (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (show parabolicResidualFlag 2 = twoFlag from by exact source_twoFlag_eq h))
    (pCore_map_iso 2 (MulEquiv.subgroupCongr (show parabolicResidualFlag 2 = twoFlag from by exact source_twoFlag_eq h)))).trans twoFlagQuotientEquiv

noncomputable def sourceThreeFlagQuotientEquiv
    (h : parabolicResidual 3 = parabolicThreeLargeBlock) :
    (parabolicResidualFlag 3 ⧸ pCore 2 (parabolicResidualFlag 3)) ≃* SL(3, ZMod 2) :=
  (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (show parabolicResidualFlag 3 = threeFlag from by exact source_threeFlag_eq h))
    (pCore_map_iso 2 (MulEquiv.subgroupCongr (show parabolicResidualFlag 3 = threeFlag from by exact source_threeFlag_eq h)))).trans threeFlagQuotientEquiv

@[simp] theorem sourceTwoFlagQuotientEquiv_mk
    (h : parabolicResidual 2 = parabolicTwoLargeBlock) (g : parabolicResidualFlag 2) :
    sourceTwoFlagQuotientEquiv h (QuotientGroup.mk' _ g) =
      twoLargeHom (Subgroup.inclusion (parabolicResidualFlag_le 2 (by decide)) g) := rfl

@[simp] theorem sourceThreeFlagQuotientEquiv_mk
    (h : parabolicResidual 3 = parabolicThreeLargeBlock) (g : parabolicResidualFlag 3) :
    sourceThreeFlagQuotientEquiv h (QuotientGroup.mk' _ g) =
      threeLargeHom (Subgroup.inclusion (parabolicResidualFlag_le 3 (by decide)) g) := rfl

/-- The image of the actual residual under the actual quotient of its flag join. -/
noncomputable def residualImageHom (k : ℕ) : parabolicResidual k →*
    (parabolicResidualFlag k ⧸ pCore 2 (parabolicResidualFlag k)) :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion
    (show parabolicResidual k ≤ parabolicResidualFlag k from le_sup_left))

/-- The source projection kernel is exactly the intersection with the source radical. -/
theorem residualImageHom_ker (k : ℕ) :
    (residualImageHom k).ker = (parabolicResidualTwoCore k).subgroupOf (parabolicResidual k) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change QuotientGroup.mk' _ (Subgroup.inclusion
    (show parabolicResidual k ≤ parabolicResidualFlag k from le_sup_left) g) = 1 ↔
      g.val ∈ (pCore 2 (parabolicResidualFlag k)).map (parabolicResidualFlag k).subtype
  exact (QuotientGroup.eq_one_iff _).trans
    (Subgroup.mem_map_iff_mem (parabolicResidualFlag k).subtype_injective).symm

instance sourceRadical_normal_in_residual (k : ℕ) :
    ((parabolicResidualTwoCore k).subgroupOf (parabolicResidual k)).Normal := by
  rw [← residualImageHom_ker]
  infer_instance

theorem residualImageHom_two_surjective
    (h : parabolicResidual 2 = parabolicTwoLargeBlock) :
    Function.Surjective (residualImageHom 2) := by
  intro x
  obtain ⟨g, hg⟩ := twoResidualHom_surjective (sourceTwoFlagQuotientEquiv h x)
  refine ⟨(MulEquiv.subgroupCongr h).symm g, (sourceTwoFlagQuotientEquiv h).injective ?_⟩
  exact hg

theorem residualImageHom_three_surjective
    (h : parabolicResidual 3 = parabolicThreeLargeBlock) :
    Function.Surjective (residualImageHom 3) := by
  intro x
  obtain ⟨g, hg⟩ := threeResidualHom_surjective (sourceThreeFlagQuotientEquiv h x)
  refine ⟨(MulEquiv.subgroupCongr h).symm g, (sourceThreeFlagQuotientEquiv h).injective ?_⟩
  exact hg

theorem residualImageHom_two_range
    (h : parabolicResidual 2 = parabolicTwoLargeBlock) : (residualImageHom 2).range = ⊤ :=
  (residualImageHom 2).range_eq_top_of_surjective (residualImageHom_two_surjective h)

theorem residualImageHom_three_range
    (h : parabolicResidual 3 = parabolicThreeLargeBlock) : (residualImageHom 3).range = ⊤ :=
  (residualImageHom 3).range_eq_top_of_surjective (residualImageHom_three_surjective h)

/-- A genuine equivalence for the actual source residual image. -/
noncomputable def sourceTwoImageEquiv
    (h : parabolicResidual 2 = parabolicTwoLargeBlock) :
    (residualImageHom 2).range ≃* SL(3, ZMod 2) :=
  (MulEquiv.subgroupCongr (residualImageHom_two_range h)).trans
    (Subgroup.topEquiv.trans (sourceTwoFlagQuotientEquiv h))

noncomputable def sourceThreeImageEquiv
    (h : parabolicResidual 3 = parabolicThreeLargeBlock) :
    (residualImageHom 3).range ≃* SL(3, ZMod 2) :=
  (MulEquiv.subgroupCongr (residualImageHom_three_range h)).trans
    (Subgroup.topEquiv.trans (sourceThreeFlagQuotientEquiv h))

/-- The actual L₁ modulo its intersection with R₁. -/
noncomputable def sourceTwoResidualQuotientEquiv
    (h : parabolicResidual 2 = parabolicTwoLargeBlock) :
    (parabolicResidual 2 ⧸ (parabolicResidualTwoCore 2).subgroupOf (parabolicResidual 2)) ≃*
      SL(3, ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq (residualImageHom_ker 2).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _ (residualImageHom_two_surjective h)).trans
      (sourceTwoFlagQuotientEquiv h))

/-- The actual L₃ modulo its intersection with R₃. -/
noncomputable def sourceThreeResidualQuotientEquiv
    (h : parabolicResidual 3 = parabolicThreeLargeBlock) :
    (parabolicResidual 3 ⧸ (parabolicResidualTwoCore 3).subgroupOf (parabolicResidual 3)) ≃*
      SL(3, ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq (residualImageHom_ker 3).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _ (residualImageHom_three_surjective h)).trans
      (sourceThreeFlagQuotientEquiv h))

@[simp] theorem sourceTwoResidualQuotientEquiv_mk
    (h : parabolicResidual 2 = parabolicTwoLargeBlock) (g : parabolicResidual 2) :
    sourceTwoResidualQuotientEquiv h (QuotientGroup.mk' _ g) =
      twoLargeHom (Subgroup.inclusion (parabolicResidual_le 2) g) := rfl

@[simp] theorem sourceThreeResidualQuotientEquiv_mk
    (h : parabolicResidual 3 = parabolicThreeLargeBlock) (g : parabolicResidual 3) :
    sourceThreeResidualQuotientEquiv h (QuotientGroup.mk' _ g) =
      threeLargeHom (Subgroup.inclusion (parabolicResidual_le 3) g) := rfl

/-- The source residual image is identified by the literal lower-right block. -/
theorem sourceTwoImageEquiv_entry
    (h : parabolicResidual 2 = parabolicTwoLargeBlock) (g : parabolicResidual 2) (i j : Fin 3) :
    (sourceTwoImageEquiv h ((residualImageHom 2).rangeRestrict g)).val i j =
      g.val.val ⟨2+i.val, by omega⟩ ⟨2+j.val, by omega⟩ :=
  parabolicLeviHom_snd_entry 2 (by decide) (Subgroup.inclusion (parabolicResidual_le 2) g) i j

/-- The source residual image is identified by the literal upper-left block. -/
theorem sourceThreeImageEquiv_entry
    (h : parabolicResidual 3 = parabolicThreeLargeBlock) (g : parabolicResidual 3) (i j : Fin 3) :
    (sourceThreeImageEquiv h ((residualImageHom 3).rangeRestrict g)).val i j =
      g.val.val (Fin.castLE (by decide) i) (Fin.castLE (by decide) j) :=
  parabolicLeviHom_fst_entry 3 (by decide) (Subgroup.inclusion (parabolicResidual_le 3) g) i j

end Representation.SL5ExteriorSquare.MiddleCore
