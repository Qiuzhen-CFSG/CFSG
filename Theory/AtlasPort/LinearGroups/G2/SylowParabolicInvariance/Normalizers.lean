module

public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter
public import Theory.AtlasPort.LinearGroups.G2.LocalNormalizer
public import Theory.AtlasPort.LinearGroups.G2.DistinguishedPlane
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification.Stabilizer

/-!
# Intrinsic root normalizers in the split G₂ model

The displacements of the highest-root group span the standard zero-product
plane; those of the two long-root groups span the distinguished three-space.
Consequently their normalizers preserve the corresponding line and point.
The converse follows from the root, torus, and Weyl conjugation formulas.

These equalities support the invariant-parabolic argument in
Aschbacher–Smith, 2.3.9(7), printed p.526. The coordinate definitions and
geometric stabilizer identifications are from the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
open Atlas.G2.LieParabolicSetup
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification

namespace Atlas.G2.SylowParabolicInvariance
variable {F : Type*} [Field F]

private theorem map_displacement (g h : Model F) (x : Carrier F) :
    g.val (h.val x - x) = (g * h * g⁻¹).val (g.val x) - g.val x := by
  rw [map_sub]
  congr 1
  change g.val (h.val x) = g.val (h.val (g.val.symm (g.val x)))
  rw [LinearEquiv.symm_apply_apply]

private theorem highestRoot_displacement (h : Model F) (hh : h ∈ highestRoot)
    (x : Carrier F) : h.val x - x ∈ standardPlane := by
  obtain ⟨a,rfl⟩ := hh
  rw [mem_standardPlane_iff_coordinates]
  simp [highestRootHom, rootA, rootAEquiv, rootALinear, rootAApply]

private theorem rootA_displacement_zero :
    (rootA (-1 : F)).val (basisVector 6) - basisVector 6 = basisVector 0 := by
  funext i
  fin_cases i <;> simp [rootA, rootAEquiv, rootALinear, rootAApply, basisVector]

private theorem rootA_displacement_one :
    (rootA (1 : F)).val (basisVector 7) - basisVector 7 = basisVector 1 := by
  funext i
  fin_cases i <;> simp [rootA, rootAEquiv, rootALinear, rootAApply, basisVector]

private theorem rootB_displacement_two :
    (rootB (1 : F)).val (basisVector 7) - basisVector 7 = basisVector 2 := by
  funext i
  fin_cases i <;> simp [rootB, rootBEquiv, rootBLinear, rootBApply, basisVector]

private theorem normalizer_highestRoot_le :
    Subgroup.normalizer (highestRoot (F := F) : Set (Model F)) ≤ parabolic₁ := by
  intro g hg
  rw [shortParabolic_eq_lineStabilizer]
  apply fixes_standardLine_of_basis_images
  · rw [← rootA_displacement_zero, map_displacement]
    apply highestRoot_displacement
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp ⟨Multiplicative.ofAdd (-1),rfl⟩
  · rw [← rootA_displacement_one, map_displacement]
    apply highestRoot_displacement
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp ⟨Multiplicative.ofAdd 1,rfl⟩

private theorem longRoot_displacement (h : Model F) (hh : h ∈ longRootLocal)
    (x : Carrier F) : h.val x - x ∈ distinguishedPlane := by
  obtain ⟨a,rfl⟩ := hh
  intro i hi
  fin_cases i <;> simp_all [longRootHom, rootA, rootB, rootAEquiv, rootBEquiv,
    rootALinear, rootBLinear, rootAApply, rootBApply]

private theorem normalizer_longRootLocal_le :
    Subgroup.normalizer (longRootLocal (F := F) : Set (Model F)) ≤ parabolic₂ := by
  intro g hg
  rw [parabolic₂, parabolic_eq_pointStabilizer]
  have hdisp (h : Model F) (hh : h ∈ longRootLocal) (x : Carrier F) :
      g.val (h.val x - x) ∈ distinguishedPlane := by
    rw [map_displacement]
    exact longRoot_displacement _ ((Subgroup.mem_normalizer_iff.mp hg _).mp hh) _
  have h0 : g.val (basisVector 0) ∈ distinguishedPlane := by
    rw [← rootA_displacement_zero]
    exact hdisp _ (rootA_mem_longRootLocal _) _
  have h1 : g.val (basisVector 1) ∈ distinguishedPlane := by
    rw [← rootA_displacement_one]
    exact hdisp _ (rootA_mem_longRootLocal _) _
  have h2 : g.val (basisVector 2) ∈ distinguishedPlane := by
    rw [← rootB_displacement_two]
    exact hdisp _ (rootB_mem_longRootLocal _) _
  apply plane_preserver_mem_pointStabilizer
  intro x hx
  have he : x = x 0 • basisVector 0 + x 1 • basisVector 1 + x 2 • basisVector 2 := by
    have he := distinguishedPlane_coordinates hx
    rw [he]
    funext i
    fin_cases i <;> simp [basisVector]
  rw [he, map_add, map_add, map_smul, map_smul, map_smul]
  exact distinguishedPlane.add_mem
    (distinguishedPlane.add_mem (distinguishedPlane.smul_mem _ h0)
      (distinguishedPlane.smul_mem _ h1)) (distinguishedPlane.smul_mem _ h2)

theorem normalizer_longRootLocal :
    Subgroup.normalizer (longRootLocal (F := F) : Set (Model F)) = parabolic₂ := by
  apply le_antisymm normalizer_longRootLocal_le
  rw [parabolic₂, parabolic_eq_pointStabilizer]
  exact pointStabilizer_le_longRootNormalizer

variable [CharP F 2]

theorem normalizer_highestRoot :
    Subgroup.normalizer (highestRoot (F := F) : Set (Model F)) = parabolic₁ := by
  have hl : local₁ (F := F) ≤ Subgroup.normalizer (highestRoot (F := F) : Set (Model F)) := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro g hg z ⟨a,rfl⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (local₁_le_centralizer_rootA a.toAdd hg)
    change g * rootA a.toAdd * g⁻¹ ∈ highestRoot
    rw [hc, mul_inv_cancel_right]
    exact ⟨a,rfl⟩
  apply le_antisymm normalizer_highestRoot_le
  rw [← local₁_sup_borel]
  exact sup_le hl (sup_le (unipotent_le_local₁.trans hl) (by
      apply Subgroup.le_normalizer_iff.mpr
      rintro g ⟨⟨a,b⟩,rfl⟩ z ⟨t,rfl⟩
      change torus a b * rootA t.toAdd * (torus a b)⁻¹ ∈ highestRoot
      rw [torus_rootA]
      exact ⟨Multiplicative.ofAdd _,rfl⟩))
end Atlas.G2.SylowParabolicInvariance

end
