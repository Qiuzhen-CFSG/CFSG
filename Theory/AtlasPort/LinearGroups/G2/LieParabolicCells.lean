module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The block and partner normal forms use the existing ATLAS port, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: rank-one cells in arbitrary characteristic, their local maximality
and size consequence, and triviality of the Borel core.
-/

public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Geometry
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Local cells and core of the actual G₂ parabolics

Singular-point transitivity and faithfulness kill the point-stabilizer core,
hence also the Borel core. The long parabolic's scalar and partner normal form
reduces to an SL₂ block; triangular elimination gives its two Borel cells.
The torus factor accompanying the Weyl reflection retains the signs in odd
characteristic. In particular the Borel is maximal in the long parabolic.

On the short side, reducing the first image vector in the standard null plane
gives representatives indexed by the field together with one extra point.
This bounds the short parabolic by (q+1)|B|, without a group-order hypothesis.
These local facts are used to establish whole overlap and faithfulness for
ternary completions in Aschbacher–Smith F.4.6(1), printed pp.276–277.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.SplitOctonion
open Atlas.G2.Explicit Atlas.G2.PairStabilizer
open scoped MatrixGroups
noncomputable section
namespace Atlas.G2.ParabolicCells
variable {F : Type*} [Field F]

theorem point_core : (pointStabilizer (K := F)).normalCore = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  change g = 1
  apply singular_lines_kernel_trivial
  intro p
  obtain ⟨h, hh⟩ := exists_smul_firstPoint p
  have he : (h*g*h⁻¹) • firstPoint = (firstPoint : SingularPoints F) := hg h
  rw [SemigroupAction.mul_smul, SemigroupAction.mul_smul, ← hh, inv_smul_smul] at he
  exact (MulAction.injective h) he

theorem borel_core : (borel (K := F)).normalCore = ⊥ := by
  apply le_bot_iff.mp
  exact (normalCore_mono (borel_le_parabolic₂.trans parabolic_le_pointStabilizer)).trans
    point_core.le

private theorem block_triangular (M : SL(2,F)) (hM : M.val 1 0 = 0) :
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
  exact borel.mul_mem (mem_sup_right ⟨(1,a),rfl⟩)
    (mem_sup_left (subset_closure (by simp)))

private theorem block_cells (M : SL(2,F)) :
    blockHom M ∈ borel ∨ ∃ b ∈ borel, ∃ d ∈ borel, blockHom M = b * weylR * d := by
  by_cases hc : M.val 1 0 = 0
  · exact Or.inl (block_triangular M hc)
  right
  let c : Fˣ := Units.mk0 (M.val 1 0) hc
  refine ⟨rootE (M.val 0 0 / M.val 1 0) * torus (-1) (-1),
    borel.mul_mem (mem_sup_left (subset_closure (by simp))) (mem_sup_right ⟨(-1,-1),rfl⟩),
    torus 1 c * rootE (M.val 1 1 / M.val 1 0),
    borel.mul_mem (mem_sup_right ⟨(1,c),rfl⟩) (mem_sup_left (subset_closure (by simp))), ?_⟩
  have hd : M.val 0 0 * M.val 1 1 - M.val 0 1 * M.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using M.prop
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [blockHom,blockEquiv,blockLinear,torus,torusEquiv,torusLinear,torusWeights,
      rootE,rootEEquiv,rootELinear,rootEApply,weylR,weylREquiv,weylRLinear,weylRApply,c]
  all_goals field_simp
  all_goals grind only


/-- Both rank-one Bruhat cells in the long parabolic, in every characteristic. -/
theorem long_cells (g : Model F) (hg : g ∈ parabolic₂) :
    g ∈ borel ∨ ∃ b ∈ borel, ∃ d ∈ borel, g = b * weylR * d := by
  let p : pointStabilizer (K := F) :=
    ⟨g⁻¹, parabolic_eq_pointStabilizer.le (parabolic.inv_mem hg)⟩
  let n := normalizePoint p
  let r := normalizedPair n
  let c := chartReducer (partnerOf n).val
  let t := torus (lineScalar p) 1
  have hc : c ∈ borel := mem_sup_left (chartReducer_mem_unipotent _)
  have ht : t ∈ borel := mem_sup_right ⟨(lineScalar p,1),rfl⟩
  have he : g = blockHom (imageSL r)⁻¹ * (c * t⁻¹) := by
    rw [map_inv]
    have he := congrArg Subtype.val (block_imageSL r)
    change blockHom (imageSL r) = c * (t⁻¹ * g⁻¹) at he
    rw [he]
    group
  rw [he]
  have hd := borel.mul_mem hc (borel.inv_mem ht)
  rcases block_cells (imageSL r)⁻¹ with h | ⟨b,hb,d,hd',he'⟩
  · exact Or.inl (borel.mul_mem h hd)
  · exact Or.inr ⟨b,hb,d*(c*t⁻¹),borel.mul_mem hd' hd,by rw [he',mul_assoc]⟩
theorem short_cells (g : Model F) (hg : g ∈ parabolic₁) :
    g ∈ borel ∨ ∃ a : F, ∃ b ∈ borel, g = rootF a * weylS * b := by
  let x := g.val (basisVector 0)
  have hx : x ∈ shortPlane :=
    (parabolic₁_le_shortPlaneStabilizer hg).1 _ (basis_mem_shortPlane 0 (by decide))
  have hn : x ≠ 0 := fun hz =>
    first_basis_ne_zero (g.val.injective (hz.trans (map_zero g.val).symm))
  by_cases h1 : x 1 = 0
  · left
    have h0 : x 0 ≠ 0 := by
      intro h0
      apply hn
      rw [shortPlane_coordinates hx,h0,h1]
      ext i
      fin_cases i <;> rfl
    have hp : g ∈ parabolic₂ := by
      rw [parabolic₂,parabolic_eq_pointStabilizer]
      apply (mem_pointStabilizer_iff g).mpr
      refine ⟨Units.mk0 (x 0) h0, ?_⟩
      change x = _
      simp only [Units.smul_def,Units.val_mk0]
      conv_lhs => rw [shortPlane_coordinates hx]
      ext i
      fin_cases i <;> simp [basisVector,h1]
    exact parabolics_intersection.le ⟨hg,hp⟩
  · right
    let a := x 0 / x 1
    let r := weylS * rootF a
    have hr : r ∈ parabolic₁ (F := F) := parabolic₁.mul_mem
      (mem_sup_right (subset_closure (by simp)))
      (borel_le_parabolic₁ (mem_sup_left (subset_closure (by simp))))
    have hp : r*g ∈ parabolic₂ := by
      rw [parabolic₂,parabolic_eq_pointStabilizer]
      apply (mem_pointStabilizer_iff _).mpr
      refine ⟨Units.mk0 (-x 1) (neg_ne_zero.mpr h1), ?_⟩
      change weylS.val (rootF a |>.val x) = _
      simp only [Units.smul_def,Units.val_mk0]
      conv_lhs => rw [shortPlane_coordinates hx]
      ext i
      fin_cases i <;> simp [a,weylS,weylSEquiv,weylSLinear,weylSApply,
        rootF,rootFEquiv,rootFLinear,rootFApply,basisVector,h1]
    refine ⟨-a,r*g,parabolics_intersection.le ⟨parabolic₁.mul_mem hr hg,hp⟩,?_⟩
    have hs : (weylS : Model F) * weylS = 1 := by rw [←pow_two,weylS_sq]
    have hf : rootF (-a) * rootF a = (1 : Model F) := by
      rw [Atlas.G2.rootF_add,neg_add_cancel]
      apply Subtype.ext
      apply LinearEquiv.ext
      intro y
      ext i
      fin_cases i <;> simp [rootF,rootFEquiv,rootFLinear,rootFApply]
    change g = rootF (-a) * weylS * ((weylS * rootF a) * g)
    calc
      _ = (rootF (-a) * rootF a) * g := by rw [hf,one_mul]
      _ = _ := by
        have hss (z : Model F) : weylS * (weylS * z) = z := by
          rw [←mul_assoc,hs,one_mul]
        simp only [mul_assoc,hss]

theorem short_card_le [Finite F] : Nat.card (parabolic₁ (F := F)) ≤
    (Nat.card F + 1) * Nat.card (borel (K := F)) := by
  let f : Option F × borel (K := F) → parabolic₁ (F := F) := fun p =>
    match p.1 with
    | none => ⟨p.2.val,borel_le_parabolic₁ p.2.property⟩
    | some a => ⟨rootF a * weylS * p.2.val,parabolic₁.mul_mem
        (parabolic₁.mul_mem
          (borel_le_parabolic₁ (mem_sup_left (subset_closure (by simp))))
          (mem_sup_right (subset_closure (by simp)))) (borel_le_parabolic₁ p.2.property)⟩
  have hf : Function.Surjective f := by
    rintro ⟨g,hg⟩
    rcases short_cells g hg with hb | ⟨a,b,hb,hg⟩
    · exact ⟨(none,⟨g,hb⟩),rfl⟩
    · exact ⟨(some a,⟨b,hb⟩),Subtype.ext hg.symm⟩
  simpa only [Nat.card_prod,Finite.card_option] using Nat.card_le_card_of_surjective f hf

theorem long_maximal (H : Subgroup (Model F)) (hB : borel ≤ H) (hH : H ≤ parabolic₂) :
    H = borel ∨ H = parabolic₂ := by
  by_cases h : H ≤ borel
  · exact Or.inl (le_antisymm h hB)
  right
  obtain ⟨g,hg,hout⟩ := SetLike.not_le_iff_exists.mp h
  rcases long_cells g (hH hg) with hb | ⟨b,hb,d,hd,he⟩
  · exact (hout hb).elim
  have hw : (weylR : Model F) ∈ H := by
    have hh := H.mul_mem (H.mul_mem (H.inv_mem (hB hb)) hg) (H.inv_mem (hB hd))
    rw [he] at hh
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh
  apply le_antisymm hH
  exact sup_le hB ((closure_le H).mpr (by simpa using hw))
end Atlas.G2.ParabolicCells
