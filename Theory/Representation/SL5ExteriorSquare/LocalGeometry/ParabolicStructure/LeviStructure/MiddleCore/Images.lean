module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.MiddleCore.Core

/-!
# The actual large-block images in the middle flag quotients

The small-block kernels surject onto Hᵢ/O₂(Hᵢ). Their projection kernels
are intersections with the embedded radicals, not the whole radicals.
The first isomorphism theorem gives the corresponding marked SL₃ quotients.

Source: Aschbacher–Smith, Lemma 12.5.2(1–2), printed p.817/PDF p.834.
-/

@[expose] public section
open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare.MiddleCore
open SL5TenDimensional

/-- The literal quotient projection restricted to the large-block subgroup. -/
noncomputable def twoImageHom : parabolicTwoLargeBlock →* (twoFlag ⧸ pCore 2 twoFlag) :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion (show parabolicTwoLargeBlock ≤ twoFlag from le_sup_left))

/-- The literal quotient projection for the reversed block convention. -/
noncomputable def threeImageHom : parabolicThreeLargeBlock →* (threeFlag ⧸ pCore 2 threeFlag) :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion (show parabolicThreeLargeBlock ≤ threeFlag from le_sup_left))

@[simp] theorem twoImageHom_marked (g : parabolicTwoLargeBlock) :
    twoFlagQuotientEquiv (twoImageHom g) = twoResidualHom g := rfl

@[simp] theorem threeImageHom_marked (g : parabolicThreeLargeBlock) :
    threeFlagQuotientEquiv (threeImageHom g) = threeResidualHom g := rfl

theorem twoImageHom_surjective : Function.Surjective twoImageHom := by
  intro x
  obtain ⟨g, hg⟩ := twoResidualHom_surjective (twoFlagQuotientEquiv x)
  exact ⟨g, twoFlagQuotientEquiv.injective hg⟩

theorem threeImageHom_surjective : Function.Surjective threeImageHom := by
  intro x
  obtain ⟨g, hg⟩ := threeResidualHom_surjective (threeFlagQuotientEquiv x)
  exact ⟨g, threeFlagQuotientEquiv.injective hg⟩

theorem twoImageHom_range : twoImageHom.range = ⊤ :=
  twoImageHom.range_eq_top_of_surjective twoImageHom_surjective

theorem threeImageHom_range : threeImageHom.range = ⊤ :=
  threeImageHom.range_eq_top_of_surjective threeImageHom_surjective

theorem twoImageHom_ker : twoImageHom.ker = twoRadical.subgroupOf parabolicTwoLargeBlock := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← twoCore_map]
  change QuotientGroup.mk' _ (Subgroup.inclusion (show parabolicTwoLargeBlock ≤ twoFlag from le_sup_left) g) = 1 ↔ _
  exact (QuotientGroup.eq_one_iff _).trans
    (Subgroup.mem_map_iff_mem twoFlag.subtype_injective).symm

theorem threeImageHom_ker : threeImageHom.ker = threeRadical.subgroupOf parabolicThreeLargeBlock := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← threeCore_map]
  change QuotientGroup.mk' _ (Subgroup.inclusion (show parabolicThreeLargeBlock ≤ threeFlag from le_sup_left) g) = 1 ↔ _
  exact (QuotientGroup.eq_one_iff _).trans
    (Subgroup.mem_map_iff_mem threeFlag.subtype_injective).symm

theorem twoResidualHom_ker : twoResidualHom.ker = twoRadical.subgroupOf parabolicTwoLargeBlock := by
  rw [← twoImageHom_ker]
  ext g
  change twoResidualHom g = 1 ↔ twoImageHom g = 1
  rw [← twoImageHom_marked, MulEquiv.map_eq_one_iff]

theorem threeResidualHom_ker : threeResidualHom.ker = threeRadical.subgroupOf parabolicThreeLargeBlock := by
  rw [← threeImageHom_ker]
  ext g
  change threeResidualHom g = 1 ↔ threeImageHom g = 1
  rw [← threeImageHom_marked, MulEquiv.map_eq_one_iff]

/-- The ambient kernel is the intersection with the radical. -/
theorem twoImageHom_ker_map : twoImageHom.ker.map parabolicTwoLargeBlock.subtype =
    parabolicTwoLargeBlock ⊓ twoRadical := by
  rw [twoImageHom_ker, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem threeImageHom_ker_map : threeImageHom.ker.map parabolicThreeLargeBlock.subtype =
    parabolicThreeLargeBlock ⊓ threeRadical := by
  rw [threeImageHom_ker, Subgroup.subgroupOf_map_subtype, inf_comm]

instance twoRadical_normal_in_largeBlock : (twoRadical.subgroupOf parabolicTwoLargeBlock).Normal := by
  rw [← twoImageHom_ker]
  infer_instance

instance threeRadical_normal_in_largeBlock : (threeRadical.subgroupOf parabolicThreeLargeBlock).Normal := by
  rw [← threeImageHom_ker]
  infer_instance

/-- The large-block subgroup modulo its intersection with O₂(H₂). -/
noncomputable def twoResidualQuotientEquiv :
    (parabolicTwoLargeBlock ⧸ twoRadical.subgroupOf parabolicTwoLargeBlock) ≃* SL(3, ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq twoResidualHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective twoResidualHom twoResidualHom_surjective)

/-- The large-block subgroup modulo its intersection with O₂(H₃). -/
noncomputable def threeResidualQuotientEquiv :
    (parabolicThreeLargeBlock ⧸ threeRadical.subgroupOf parabolicThreeLargeBlock) ≃* SL(3, ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq threeResidualHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective threeResidualHom threeResidualHom_surjective)

@[simp] theorem twoResidualQuotientEquiv_mk (g : parabolicTwoLargeBlock) :
    twoResidualQuotientEquiv (QuotientGroup.mk' _ g) = twoResidualHom g := rfl

@[simp] theorem threeResidualQuotientEquiv_mk (g : parabolicThreeLargeBlock) :
    threeResidualQuotientEquiv (QuotientGroup.mk' _ g) = threeResidualHom g := rfl

/-- The image identification retains the literal lower-right block. -/
theorem twoImageHom_entry (g : parabolicTwoLargeBlock) (i j : Fin 3) :
    (twoFlagQuotientEquiv (twoImageHom g)).val i j =
      g.val.val ⟨2+i.val, by omega⟩ ⟨2+j.val, by omega⟩ :=
  twoFlagHom_entry (Subgroup.inclusion (show parabolicTwoLargeBlock ≤ twoFlag from le_sup_left) g) i j

/-- The image identification retains the literal upper-left block. -/
theorem threeImageHom_entry (g : parabolicThreeLargeBlock) (i j : Fin 3) :
    (threeFlagQuotientEquiv (threeImageHom g)).val i j =
      g.val.val (Fin.castLE (by decide) i) (Fin.castLE (by decide) j) :=
  threeFlagHom_entry (Subgroup.inclusion (show parabolicThreeLargeBlock ≤ threeFlag from le_sup_left) g) i j

end Representation.SL5ExteriorSquare.MiddleCore
