module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPlaneCentralizer
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.Mathieu.M24.LocalGeometry.TrioNormalizerControl
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.FixedSpace

/-!
# Stabilizing the original M24 cocode plane

The pointwise fixer calculation recovers the native trio. Conjugating its
intrinsic two-core shows that every setwise plane stabilizer preserves the
same trio, so the plane stabilizer is exactly the trio stabilizer. For a
perfect actor with two-group kernel in M24, the symmetric-three factor of
the affine trio action vanishes. Its plane-action kernel is consequently a
two-group. This supplies the two-core assertion for the original local
residual in source 8.2.6(3), through MathieuPlaneCore and the chosen-module
consumer NonFFSourceMathieuM24Component.
Source: Aschbacher--Smith H.15.6 and 8.2.6, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open PairOvergroups PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
/-- The actual setwise stabilizer of the plane is precisely the native trio stabilizer. -/
theorem plane_stabilizer_eq_trio :
    subspaceStabilizer cocodeRepresentation standardPlaneMap.range =
      trioStabilizer standardTrio := by
  apply le_antisymm
  · intro g hg
    apply (TrioNormalSeeds.conj_core_le_iff g).mp
    rintro _ ⟨x,hx,rfl⟩
    apply plane_fixer_mem_trio
    intro v
    have hinv := (subspaceStabilizer cocodeRepresentation standardPlaneMap.range).inv_mem hg
    obtain ⟨w,hw⟩ := (hinv (standardPlaneMap v)).mpr (LinearMap.mem_range_self _ _)
    obtain ⟨y,hy,rfl⟩ := hx
    have hfix : cocodeRepresentation y.val (cocodeRepresentation g⁻¹ (standardPlaneMap v)) =
        cocodeRepresentation g⁻¹ (standardPlaneMap v) := by
      rw [←hw,standardPlaneMap_fixed w y hy]
    change cocodeRepresentation (g * y.val * g⁻¹) (standardPlaneMap v) = _
    simp only [map_mul,Module.End.mul_apply]
    rw [hfix]
    simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  · have hh := fixedSpace_stable_of_normalizes cocodeRepresentation
      (show trioStabilizer standardTrio ≤
        normalizer (M24ChapterHStabilizers.ElementaryFusion.trioCore : Set M24) from
        TrioNormalSeeds.normalizer_core.symm.le)
    rw [show fixedSpace cocodeRepresentation M24ChapterHStabilizers.ElementaryFusion.trioCore =
      standardPlaneMap.range from standard_fixedSpace_eq_planeRange] at hh
    exact hh

/-- In a perfect actor with a two-group M24 kernel, the plane-action
kernel is also a two-group. The symmetric-three affine factor is killed
by perfectness, and the remaining kernel consists of translations. -/
theorem perfect_plane_kernel_isTwoGroup
    {P : Type*} [Group P] [Finite P] [Group.IsPerfect P]
    (f : P →* M24) (hf : IsPGroup 2 f.ker)
    (hs : ∀ p, f p ∈ subspaceStabilizer cocodeRepresentation standardPlaneMap.range)
    (K : Subgroup P)
    (hk : ∀ k : K, ∀ v, cocodeRepresentation (f k.val) (standardPlaneMap v) =
      standardPlaneMap v) : IsPGroup 2 K := by
  let q : P →* trioStabilizer standardTrio := f.codRestrict _
    (fun p => plane_stabilizer_eq_trio ▸ hs p)
  have he : q.ker = f.ker := by
    ext p
    change (⟨f p,_⟩ : trioStabilizer standardTrio) = 1 ↔ f p = 1
    exact Subtype.ext_iff
  have hq : IsPGroup 2 q.ker := he.symm ▸ hf
  let χ := (MonoidHom.fst _ _).comp (standardAffineHom.comp q)
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  have hχ (p : P) : χ p = 1 := by
    have hp : p ∈ solvableResidual P := by rw [solvableResidual_eq_top]; trivial
    have hm := map_solvableResidual_le χ (mem_map_of_mem χ hp)
    rw [solvableResidual_eq_bot] at hm
    exact hm
  have hle : K ≤ (pCore 2 (trioStabilizer standardTrio)).comap q := by
    intro k hkK
    exact plane_fixer_in_core (q k) (hχ k) (hk ⟨k,hkK⟩)
  exact (pCore_isPGroup.comap_of_ker_isPGroup q hq).to_le hle

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
