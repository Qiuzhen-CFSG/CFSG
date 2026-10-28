module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane.Seed
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.Notation

/-!
# Selecting the original returning element in the plane residual

An even syntheme rotation preserves the source plane and moves its point.
Its odd order places it in the two-residual of the plane stabilizer image;
functoriality of the two-residual then lifts it into the literal subgroup
L₂ = O²(N_L(V₂)). Equivariance preserves both flag assertions under this
lift, without assuming a returning element or a fusion witness.

Source: Aschbacher–Smith,13.5.16, printed p.921, in the ordinary natural
A₆ action supplied by13.2.1 and13.3.3.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

include d

theorem plane_residual_lift (r : Equiv.Perm (Fin 6))
    (hr : r ∈ alternatingGroup (Fin 6))
    (hp : r ∈ flagStabilizer (Section07.NaturalAction.image d V₂)) (hr3 : r ^ 3 = 1) :
    ∃ y : D.L, y.val ∈ Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂ ∧
      localMap d y = r := by
  let K := D.L ⊓ normalizer (V₂ : Set G)
  let R := (pResidual 2 K).map K.subtype
  let J := K.subgroupOf D.L
  let P := J.map (localMap d)
  have hrP : r ∈ P := by
    rw [show P = alternatingGroup (Fin 6) ⊓ flagStabilizer
      (Section07.NaturalAction.image d V₂) from
        localNormalizer_image d V₂ (d.plane_le_seed.trans d.seed_le)]
    exact ⟨hr,hp⟩
  let rP : P := ⟨r,hrP⟩
  have hres : rP ∈ pResidual 2 P := by
    apply mem_pResidual_of_orderOf_coprime
    exact (by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one (show rP ^ 3 = 1 from Subtype.ext hr3))
  have hmap : (R.subgroupOf D.L).map (localMap d) = (pResidual 2 P).map P.subtype := by
    have he : R.subgroupOf D.L = (pResidual 2 J).map J.subtype := by
      apply map_injective D.L.subtype_injective
      rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans inf_le_left),
        map_embedded_pResidual, map_subgroupOf_eq_of_le inf_le_left]
    rw [he, map_embedded_pResidual]
  have hmem : r ∈ (R.subgroupOf D.L).map (localMap d) :=
    hmap.symm ▸ mem_map_of_mem P.subtype hres
  obtain ⟨y,hy,he⟩ := hmem
  exact ⟨y,hy,he⟩

theorem exists_original_returning (h : D.Hypothesis) :
    ∃ a : alternatingGroup (Fin 6),
      Section07.NaturalAction.image d D.V₁ = move a.val canonicalLine ∧
      Section07.NaturalAction.image d V₂ = move a.val canonicalPlane ∧
      ∃ y : D.L,
        y.val ∈ Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂ ∧
        localMap d y = a.val * pairRotation⁻¹ * a.val⁻¹ ∧
        y.val ∈ normalizer (V₂ : Set G) ∧ y.val ∉ D.Gz := by
  obtain ⟨a, ha, hp⟩ := QuadraticSource.source_even_flag d
  let r : Equiv.Perm (Fin 6) := a.val * pairRotation⁻¹ * a.val⁻¹
  have hr : r ∈ alternatingGroup (Fin 6) :=
    (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _
      ((alternatingGroup (Fin 6)).inv_mem ReturningPlane.rotation_even) a.val
  have hplane : r ∈ flagStabilizer (Section07.NaturalAction.image d V₂) := by
    rw [hp, flagStabilizer_move, flagStabilizer_plane]
    exact mem_map_of_mem (MulAut.conj a.val).toMonoidHom
      (H2.inv_mem ReturningPlane.rotation_plane)
  have hr3 : r ^ 3 = 1 := by
    change ((MulAut.conj a.val) pairRotation⁻¹) ^ 3 = 1
    rw [← map_pow, inv_pow, show pairRotation ^ 3 = 1 by decide +kernel, inv_one, map_one]
  obtain ⟨y,hy,hyr⟩ := plane_residual_lift d r hr hplane hr3
  refine ⟨a,ha,hp,y,hy,hyr,?_,?_⟩
  · apply (localNormalizer_mem d V₂ (d.plane_le_seed.trans d.seed_le) y).mpr
    rw [hyr]
    exact hplane
  · intro hyG
    have hyn : y.val ∈ normalizer (D.V₁ : Set G) := h.normalizer_point_eq.symm ▸ hyG
    have hpt := (localNormalizer_mem d D.V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) y).mp hyn
    rw [hyr,ha,flagStabilizer_move,flagStabilizer_line] at hpt
    have hh : pairRotation⁻¹ ∈ H1 := by
      have hm : (MulAut.conj a.val) pairRotation⁻¹ ∈
          H1.map (MulAut.conj a.val).toMonoidHom := hpt
      simpa only [MulEquiv.symm_apply_apply] using (mem_map_equiv).mp hm
    exact ReturningPlane.rotation_not_point (by simpa only [inv_inv] using H1.inv_mem hh)

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane
end
