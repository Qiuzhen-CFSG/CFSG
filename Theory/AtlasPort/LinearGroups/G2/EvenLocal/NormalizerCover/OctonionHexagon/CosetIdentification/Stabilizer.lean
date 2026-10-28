module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The scalar and partner normalization proof adapts
Atlas/LinearGroups/G2/Parabolic.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: identify the flag and short-line stabilizers, using the existing
CFSG port's normalizations and new upper-triangular block calculation.
-/

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification.Transitivity

/-!
# The short parabolic is the zero-product line stabilizer

The positive roots, split torus and short Weyl element preserve the coordinate
plane. The root `rootF` and short Weyl element act transitively on its points.
For the converse, normalize a line stabilizer to fix the first point. The
existing scalar and partner normalizations reduce it to an SL₂ block. Plane
preservation forces the block to be upper triangular, hence in the Borel.

The coordinate formulas and the scalar/partner/SL₂ normalizations are from
the licensed ATLAS port (see the imported modules and LICENSES/ATLAS.txt).
Source context: the actual split G₂ geometry used for Aschbacher--Smith,
Theorem 0.1.2(1), printed pp.3--4 and pp.481--482.
-/

public section

open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Explicit Atlas.G2.PairStabilizer
open scoped MatrixGroups
namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
variable {F : Type*} [Field F]
open LieParabolicSetup

theorem fixes_standardLine_of_basis_images (g : Model F)
    (h0 : g.val (basisVector 0) ∈ standardPlane)
    (h1 : g.val (basisVector 1) ∈ standardPlane) : g • (standardLine (F := F)) = (standardLine (F := F)) := by
  apply Subtype.ext
  change standardPlane.map g.val.toLinearMap = standardPlane
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.map_le_iff_le_comap]
    exact Submodule.span_le.mpr (by rintro x (rfl | rfl) <;> assumption)
  · exact g.val.finrank_map_eq _

theorem unipotent_le_lineStabilizer : unipotent (K := F) ≤
    MulAction.stabilizer (Model F) (standardLine (F := F)) := by
  intro g hg
  rw [unipotent_eq_range] at hg
  obtain ⟨t,rfl⟩ := hg
  apply fixes_standardLine_of_basis_images
  all_goals rw [mem_standardPlane_iff_coordinates]
  all_goals simp [unipotentProduct,basisVector,rootA,rootB,rootC,rootD,rootE,rootF,
    rootAEquiv,rootBEquiv,rootCEquiv,rootDEquiv,rootEEquiv,rootFEquiv,
    rootALinear,rootBLinear,rootCLinear,rootDLinear,rootELinear,rootFLinear,
    rootAApply,rootBApply,rootCApply,rootDApply,rootEApply,rootFApply]

theorem torus_le_lineStabilizer : splitTorus (K := F) ≤
    MulAction.stabilizer (Model F) (standardLine (F := F)) := by
  rintro g ⟨⟨a,b⟩,rfl⟩
  apply fixes_standardLine_of_basis_images
  all_goals rw [mem_standardPlane_iff_coordinates]
  all_goals simp [torusHom,torus,torusEquiv,torusLinear,torusWeights,basisVector]

theorem borel_le_lineStabilizer : borel (K := F) ≤
    MulAction.stabilizer (Model F) (standardLine (F := F)) :=
  sup_le unipotent_le_lineStabilizer torus_le_lineStabilizer

theorem weylS_fixes_standardLine : (weylS : Model F) • (standardLine (F := F)) = (standardLine (F := F)) := by
  apply fixes_standardLine_of_basis_images
  all_goals rw [mem_standardPlane_iff_coordinates]
  all_goals simp [weylS,weylSEquiv,weylSLinear,weylSApply,basisVector]

theorem shortParabolic_le_lineStabilizer : parabolic₁ (F := F) ≤
    MulAction.stabilizer (Model F) (standardLine (F := F)) := by
  apply sup_le borel_le_lineStabilizer
  apply (Subgroup.closure_le _).mpr
  rintro g (rfl : g = weylS)
  exact weylS_fixes_standardLine

theorem rootF_mem_shortParabolic (a : F) : rootF a ∈ parabolic₁ :=
  borel_le_parabolic₁ (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))

theorem weylS_mem_shortParabolic : (weylS : Model F) ∈ parabolic₁ :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem standardPlane_vector_reduction (x : Carrier F) (hx : x ∈ standardPlane)
    (hn : x ≠ 0) :
    ∃ g ∈ parabolic₁ (F := F), ∃ a : F, a ≠ 0 ∧ g.val x = a • basisVector 0 := by
  obtain ⟨h2,h3,h4,h5,h6,h7⟩ := (mem_standardPlane_iff_coordinates x).mp hx
  by_cases h1 : x 1 = 0
  · have he : x = x 0 • basisVector 0 := by
      funext i
      fin_cases i <;> simp [basisVector,h1,h2,h3,h4,h5,h6,h7]
    refine ⟨1,parabolic₁.one_mem,x 0,?_,he⟩
    intro h0
    apply hn
    rw [he,h0,zero_smul]
  · refine ⟨weylS * rootF (x 0 / x 1),
      parabolic₁.mul_mem weylS_mem_shortParabolic (rootF_mem_shortParabolic _),
      -x 1,neg_ne_zero.mpr h1,?_⟩
    funext i
    fin_cases i <;> simp [weylS,weylSEquiv,weylSLinear,weylSApply,
      rootF,rootFEquiv,rootFLinear,rootFApply,basisVector,h2,h3,h4,h5,h6,h7]
    field_simp
    ring

theorem standardLine_point_reduction (p : SingularPoints F)
    (hp : pointOnLine p (standardLine (F := F))) :
    ∃ g ∈ parabolic₁ (F := F), g • p = firstPoint := by
  obtain ⟨g,hg,a,ha,he⟩ := standardPlane_vector_reduction p.val.rep
    ((pointOnLine_iff p (standardLine (F := F))).mp hp) p.val.rep_nonzero
  refine ⟨g,hg,?_⟩
  rw [← singularPointMk_rep F p,singularPointMk_smul,firstPoint]
  apply Subtype.ext
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact ⟨a,he.symm⟩

theorem block_lower_left_zero_of_fixes_line (M : Matrix.SpecialLinearGroup (Fin 2) F)
    (hM : blockHom M • (standardLine (F := F)) = standardLine) : M.val 1 0 = 0 := by
  have hx := (mem_line_smul (blockHom M) standardLine (basisVector 1)).mpr
    (Submodule.subset_span (by simp))
  rw [hM] at hx
  have h2 := ((mem_standardPlane_iff_coordinates _).mp hx).1
  simpa [blockHom,blockEquiv,blockLinear,basisVector] using h2

theorem block_mem_borel_of_lower_left_zero (M : Matrix.SpecialLinearGroup (Fin 2) F)
    (hM : M.val 1 0 = 0) : blockHom M ∈ borel := by
  have hd : M.val 0 0 * M.val 1 1 = 1 := by
    simpa only [Matrix.det_fin_two,hM,mul_zero,sub_zero] using M.property
  have ha : M.val 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have he : M.val 1 1 = (M.val 0 0)⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff ha).mpr
    simpa only [mul_comm] using hd
  let a : Fˣ := Units.mk0 (M.val 0 0) ha
  have hb : blockHom M = torus 1 a * rootE (M.val 0 1 / M.val 0 0) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change blockLinear M.val x = (torus 1 a).val ((rootE _).val x)
    funext i
    fin_cases i <;> simp [blockLinear,torus,torusEquiv,torusLinear,torusWeights,
      rootE,rootEEquiv,rootELinear,rootEApply,hM,he,a]
    all_goals field_simp
  rw [hb]
  apply borel.mul_mem
  · exact Subgroup.mem_sup_right ⟨(1,a),rfl⟩
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))

theorem fixingPair_lineStabilizer_le_borel (g : fixingPair (F := F))
    (hg : g.val • (standardLine (F := F)) = standardLine) : g.val ∈ borel := by
  have he : blockHom (imageSL g) = g.val := congrArg Subtype.val (block_imageSL g)
  rw [← he] at hg ⊢
  exact block_mem_borel_of_lower_left_zero _ (block_lower_left_zero_of_fixes_line _ hg)

theorem fixingFirstVector_lineStabilizer_le_borel (g : fixingFirstVector (K := F))
    (hg : g.val • (standardLine (F := F)) = standardLine) : g.val ∈ borel := by
  have hc : chartReducer (partnerOf g).val ∈ borel :=
    Subgroup.mem_sup_left (chartReducer_mem_unipotent _)
  have hline : (normalizedPair g).val • (standardLine (F := F)) = standardLine := by
    change (chartReducer (partnerOf g).val * g.val) • standardLine = standardLine
    rw [SemigroupAction.mul_smul,hg]
    exact borel_le_lineStabilizer hc
  have hn := fixingPair_lineStabilizer_le_borel (normalizedPair g) hline
  have h := borel.mul_mem (borel.inv_mem hc) hn
  change (chartReducer (partnerOf g).val)⁻¹ *
    ((chartReducer (partnerOf g).val) * g.val) ∈ borel at h
  simpa only [inv_mul_cancel_left] using h

theorem pointStabilizer_lineStabilizer_le_borel (g : pointStabilizer (K := F))
    (hg : g.val • (standardLine (F := F)) = standardLine) : g.val ∈ borel := by
  have ht : torus (lineScalar g) 1 ∈ borel := Subgroup.mem_sup_right ⟨(lineScalar g,1),rfl⟩
  have hline : (normalizePoint g).val • (standardLine (F := F)) = standardLine := by
    change ((torus (lineScalar g) 1)⁻¹ * g.val) • standardLine = standardLine
    rw [SemigroupAction.mul_smul,hg]
    exact borel_le_lineStabilizer (borel.inv_mem ht)
  have hn := fixingFirstVector_lineStabilizer_le_borel (normalizePoint g) hline
  have h := borel.mul_mem ht hn
  change (torus (lineScalar g) 1) * ((torus (lineScalar g) 1)⁻¹ * g.val) ∈ borel at h
  simpa only [mul_inv_cancel_left] using h

/-- The stabilizer of the actual standard flag is the root-defined Borel. -/
theorem standardFlag_stabilizer :
    pointStabilizer (K := F) ⊓ MulAction.stabilizer (Model F) (standardLine (F := F)) =
      borel := by
  apply le_antisymm
  · intro g hg
    exact pointStabilizer_lineStabilizer_le_borel ⟨g,hg.1⟩ hg.2
  · apply le_inf
    · exact le_trans borel_le_parabolic₂ parabolic_le_pointStabilizer
    · exact borel_le_lineStabilizer

/-- The short-Weyl parabolic is the full stabilizer of the zero-product plane. -/
theorem shortParabolic_eq_lineStabilizer : parabolic₁ (F := F) =
    MulAction.stabilizer (Model F) (standardLine (F := F)) := by
  apply le_antisymm shortParabolic_le_lineStabilizer
  intro g hg
  have hp : pointOnLine (g • firstPoint) (standardLine (F := F)) := by
    rw [← (show g • standardLine = standardLine from hg)]
    exact (pointOnLine_smul_iff g firstPoint standardLine).mpr firstPoint_on_standardLine
  obtain ⟨k,hk,hp⟩ := standardLine_point_reduction (g • firstPoint) hp
  have hfix : (k*g) • (firstPoint (K := F)) = firstPoint := by
    rw [SemigroupAction.mul_smul,hp]
  have hl : (k*g) • (standardLine (F := F)) = standardLine := by
    rw [SemigroupAction.mul_smul,show g • standardLine = standardLine from hg]
    exact shortParabolic_le_lineStabilizer hk
  have hb := pointStabilizer_lineStabilizer_le_borel ⟨k*g,hfix⟩ hl
  have hh := parabolic₁.mul_mem (parabolic₁.inv_mem hk) (borel_le_parabolic₁ hb)
  simpa only [inv_mul_cancel_left] using hh

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
