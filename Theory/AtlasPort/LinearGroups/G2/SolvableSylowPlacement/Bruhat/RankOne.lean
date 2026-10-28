module

public import Theory.AtlasPort.LinearGroups.G2.Parabolic
public import Mathlib.Algebra.CharP.Two

/-!
# Two cells in the full long parabolic

Reverse the existing partner normal form to write a point stabilizer element
as an actual SL₂ block times a Borel element. A two-by-two determinant
calculation then gives the two cells `B` and `rootE(a) * R * B`. This includes
the entire point stabilizer, and uses no BN-pair or order comparison.

Source: the rank-one step in GLS III, Theorem 2.3.5
(`refs/KGroup/GLS3/chapter2.tex`). The split-octonion block and partner normal
forms are from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. The triangular block calculation also occurs in
`LieShortParabolic.Geometry`.
-/

@[expose] public section

namespace Atlas.G2.SolvableSylowPlacement.BruhatGeometry
open Atlas.SplitOctonion Explicit PairStabilizer
open scoped MatrixGroups
variable {F : Type*} [Field F]

private theorem block_mem_borel_of_lower_zero (M : SL(2,F)) (hM : M.val 1 0 = 0) :
    blockHom M ∈ borel := by
  have hd : M.val 0 0 * M.val 1 1 = 1 := by
    have h := M.prop
    rw [Matrix.det_fin_two] at h
    simpa only [hM,mul_zero,sub_zero] using h
  have ha : M.val 0 0 ≠ 0 := by intro h; simp [h] at hd
  let a : Fˣ := Units.mk0 (M.val 0 0) ha
  have hd' : M.val 1 1 = (a⁻¹ : Fˣ) := by
    change M.val 1 1 = (M.val 0 0)⁻¹
    exact eq_inv_of_mul_eq_one_right hd
  have he : blockHom M = torus 1 a * rootE (M.val 0 1 / (a : F)) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    funext i
    fin_cases i <;>
      simp [blockHom,blockEquiv,blockLinear,torus,torusEquiv,torusLinear,torusWeights,
        rootE,rootEEquiv,rootELinear,rootEApply,hM,hd',a] <;> field_simp
  rw [he]
  exact borel.mul_mem (Subgroup.mem_sup_right ⟨(1,a),rfl⟩)
    (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))

variable [CharP F 2]

private theorem block_two_cells (M : SL(2,F)) :
    blockHom M ∈ borel ∨ ∃ a : F, ∃ b ∈ borel, blockHom M = rootE a * weylR * b := by
  by_cases hc : M.val 1 0 = 0
  · exact Or.inl (block_mem_borel_of_lower_zero M hc)
  right
  let c : Fˣ := Units.mk0 (M.val 1 0) hc
  refine ⟨M.val 0 0 / M.val 1 0, torus 1 c * rootE (M.val 1 1 / M.val 1 0),
    borel.mul_mem (Subgroup.mem_sup_right ⟨(1,c),rfl⟩)
      (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))), ?_⟩
  have hd : M.val 0 0 * M.val 1 1 - M.val 0 1 * M.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using M.prop
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [blockHom,blockEquiv,blockLinear,torus,torusEquiv,torusLinear,torusWeights,
      rootE,rootEEquiv,rootELinear,rootEApply,weylR,weylREquiv,weylRLinear,weylRApply,
      c,CharTwo.neg_eq,CharTwo.sub_eq_add]
  all_goals field_simp
  · linear_combination (norm := ring_nf) -x 2 * hd
    simp [CharTwo.two_eq_zero]
  · linear_combination (norm := ring_nf) -x 6 * hd
    simp [CharTwo.two_eq_zero]


omit [CharP F 2] in
/-- Reverse the partner normal form to put the five-root part on the right. -/
private theorem parabolic_pair_borel (g : Model F) (hg : g ∈ parabolic) :
    ∃ M : SL(2,F), ∃ b ∈ borel, g = blockHom M * b := by
  let p : pointStabilizer (K := F) :=
    ⟨g⁻¹, parabolic_eq_pointStabilizer.le (parabolic.inv_mem hg)⟩
  let n := normalizePoint p
  let r := normalizedPair n
  let c := chartReducer (partnerOf n).val
  let t := torus (lineScalar p) 1
  have hc : c ∈ borel := Subgroup.mem_sup_left (chartReducer_mem_unipotent _)
  have ht : t ∈ borel := Subgroup.mem_sup_right ⟨(lineScalar p,1),rfl⟩
  refine ⟨(imageSL r)⁻¹, c * t⁻¹, borel.mul_mem hc (borel.inv_mem ht), ?_⟩
  rw [map_inv]
  have he := congrArg Subtype.val (block_imageSL r)
  change blockHom (imageSL r) = c * (t⁻¹ * g⁻¹) at he
  rw [he]
  group

/-- The long parabolic has the two usual rank-one cells, on the actual model. -/
theorem parabolic_two_cells (g : Model F) (hg : g ∈ parabolic) :
    g ∈ borel ∨ ∃ a : F, ∃ b ∈ borel, g = rootE a * weylR * b := by
  obtain ⟨M,b,hb,rfl⟩ := parabolic_pair_borel g hg
  rcases block_two_cells M with hM | ⟨a,c,hc,he⟩
  · exact Or.inl (borel.mul_mem hM hb)
  · exact Or.inr ⟨a,c*b,borel.mul_mem hc hb,by rw [he,mul_assoc]⟩

omit [CharP F 2] in
/-- Put the torus before the unipotent factor in the Borel. -/
theorem borel_torus_unipotent (b : Model F) (hb : b ∈ borel) :
    ∃ t ∈ splitTorus, ∃ v ∈ unipotent, b = t * v := by
  obtain ⟨⟨u,t⟩,he⟩ := borelProductEquiv.surjective ⟨b,hb⟩
  have he' : u.val * t.val = b := congrArg Subtype.val he
  refine ⟨t.val,t.property,t.val⁻¹*u.val*t.val, ?_, ?_⟩
  · simpa using torus_normalizes_unipotent (splitTorus.inv_mem t.property) u.property
  · rw [← he']
    group

end Atlas.G2.SolvableSylowPlacement.BruhatGeometry
