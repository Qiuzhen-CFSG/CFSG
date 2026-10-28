module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.KernelModel
public import Theory.AtlasPort.OtherSporadic.Conway.GolaySmallRestriction
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Kernel

/-!
# Order of the literal octad restriction kernel

Self-orthogonality of the Golay code determines the eighth coordinate from the
other seven octad coordinates. Restriction to seven coordinates is surjective
by the minimum weight, so the shortened sign code has dimension five and order
32. The genuine native/ATLAS Mathieu coordinate equivalence identifies the
pointwise factor with the elementary core of native octad 100, of order 16.
The semidirect-product comparison therefore gives the actual kernel order 512.
No enumeration of the Leech isometry group is involved.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1(1)–(3), pp.132–133.
Golay and Leech constructions reuse the existing CFSG ATLAS ports; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace KernelModel

private def octad : Finset Omega := support (golayBasis 0).val

private theorem mem_octad (i : Omega) : i ∈ octad ↔ (golayBasis 0).val i ≠ 0 := by
  simp [octad, support]

private theorem octad_card : octad.card = 8 := ambientOctad_weight

private def anchor : Coordinate := Classical.choice
  (Fintype.card_pos_iff.mp (by rw [coordinate_card]; decide))

private theorem anchor_mem : anchor.val ∈ octad := (mem_octad _).mpr anchor.prop

private theorem octad_word : supportWord octad = (golayBasis 0).val := by
  funext i
  rcases bit_cases ((golayBasis 0).val i) with h | h <;>
    simp [supportWord, mem_octad, h]

private theorem signCode_eq_ker : signCode = (golayRestriction (octad.erase anchor.val)).ker := by
  ext c
  constructor
  · intro hc
    funext i
    exact hc ⟨i.val, (mem_octad _).mp (Finset.mem_erase.mp i.prop).2⟩
  · intro hc i
    have hv (j : Omega) (hj : j ∈ octad.erase anchor.val) : c.val j = 0 :=
      congrFun hc ⟨j, hj⟩
    by_cases hi : i.val = anchor.val
    · have hd := golay_selfOrthogonal (golayBasis 0).prop c.val c.prop
      change binaryDot c.val (golayBasis 0).val = 0 at hd
      rw [← octad_word, tetradSignParity_dot, tetradSignParity, Finset.sum_coe_sort] at hd
      have hs : (∑ j ∈ octad.erase anchor.val, c.val j) = 0 := Finset.sum_eq_zero hv
      rw [← Finset.add_sum_erase _ _ anchor_mem, hs, add_zero] at hd
      simpa only [hi] using hd
    · exact hv i.val (Finset.mem_erase.mpr ⟨hi, (mem_octad _).mpr i.prop⟩)

theorem signCode_finrank : Module.finrank Bit signCode = 5 := by
  have hs : (octad.erase anchor.val).card = 7 := by
    rw [Finset.card_erase_of_mem anchor_mem, octad_card]
  have hr := (golayRestriction (octad.erase anchor.val)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (golay_small_restriction_surjective _ (by omega)),
    finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hs,
    golay_finrank, ← signCode_eq_ker] at hr
  omega

theorem signCode_card : Nat.card signCode = 32 := by
  rw [Module.natCard_eq_pow_finrank (K := Bit), signCode_finrank]
  simp [Bit]

def nativeOctad : Sporadic.Mathieu.M24LocalGeometry.Octad :=
  ⟨Sporadic.Mathieu.m24BlockAt 100,
    Finset.mem_image.mpr ⟨100, Finset.mem_univ _, rfl⟩⟩

theorem nativeOctad_support (i : Fin 24) :
    i ∈ nativeOctad.val ↔ (golayBasis 0).val (MathieuCode.atlasPointEquiv.symm i) ≠ 0 := by
  change i ∈ Sporadic.Mathieu.m24BlockAt 100 ↔
    (golayBasis 0 : BinaryWord) (MathieuCode.atlasPointEquiv.symm i) ≠ 0
  rw [golayBasis_coe]
  revert i
  decide +kernel

theorem native_mem_iff (g : Sporadic.Mathieu.M24) :
    Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv g ∈ pointwise ↔
      g ∈ MathieuCode.octadPointwiseKernel nativeOctad := by
  rw [MathieuCode.mem_octadPointwiseKernel]
  constructor
  · intro hg i hi
    have hh := hg ⟨MathieuCode.atlasPointEquiv.symm i, (nativeOctad_support i).mp hi⟩
    change MathieuCode.atlasPointEquiv.symm
      (g.val (MathieuCode.atlasPointEquiv (MathieuCode.atlasPointEquiv.symm i))) = _ at hh
    rw [MathieuCode.atlasPointEquiv.apply_symm_apply] at hh
    exact MathieuCode.atlasPointEquiv.symm.injective hh
  · intro hg i
    have hi : MathieuCode.atlasPointEquiv i.val ∈ nativeOctad.val :=
      (nativeOctad_support _).mpr (by simpa only [Equiv.symm_apply_apply] using i.prop)
    change MathieuCode.atlasPointEquiv.symm (g.val (MathieuCode.atlasPointEquiv i.val)) = i.val
    rw [show g.val (MathieuCode.atlasPointEquiv i.val) = _ from hg _ hi,
      Equiv.symm_apply_apply]

def nativeEquiv : MathieuCode.octadPointwiseKernel nativeOctad ≃* pointwise where
  toFun g := ⟨Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv g.val,
    (native_mem_iff g.val).mpr g.prop⟩
  invFun g := ⟨Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv.symm g.val, by
    rw [← native_mem_iff, MulEquiv.apply_symm_apply]; exact g.prop⟩
  left_inv g := Subtype.ext (MulEquiv.symm_apply_apply _ _)
  right_inv g := Subtype.ext (MulEquiv.apply_symm_apply _ _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

theorem pointwise_card : Nat.card pointwise = 16 := by
  rw [← Nat.card_congr nativeEquiv.toEquiv, ← MathieuCode.octad_core_map_eq_pointwise,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    MathieuCode.CocodeOctad.core_eq_coordinateKernel]
  exact MathieuCode.CocodeOctad.card_coordinateKernel nativeOctad

theorem model_card : Nat.card Model = 512 := by
  rw [SemidirectProduct.card, pointwise_card,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative signCode ≃ signCode), signCode_card]

end KernelModel

/-- The actual octad restriction kernel has the source order 2^9. -/
theorem kernel_card_512 : Nat.card action.ker = 512 := by
  rw [← Nat.card_congr KernelModel.kernelEquiv.toEquiv, KernelModel.model_card]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
