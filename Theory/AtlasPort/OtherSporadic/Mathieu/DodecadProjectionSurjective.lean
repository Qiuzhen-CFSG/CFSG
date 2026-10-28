/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadAffineStabilizer

/-!
# DodecadProjectionSurjective

Every element of the relevant Klein four group lifts to an affine dodecad stabilizer
element. The linear action preserves the hexacode parameter, and mask surjectivity
supplies a translation correcting the remaining binary mask.

Source: `Atlas/Mathieu/DodecadProjectionSurjective.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

theorem dodecadAffineProjection_lift (i : HexIndex) (p : DodecadParameters i)
    (b : hexPointKernel i) (hb : hexZeroLinear i b.val p.1.val = p.1.val) :
    ∃ x : dodecadAffineStabilizer i p, x.val.right = b := by
  let g := tetradPointStabilizerEquiv i (SemidirectProduct.inr b)
  obtain ⟨r,hr⟩ := dodecad_linear_word i p.1.val p.2.val b
  rw [hb] at hr
  have hri : r.val (hexIndexEquiv i) = 1 := by
    have hc := tetrad_fix_preserves_containment i g _ (dodecadParametersSupport i p).prop
    change tetrad i ⊆ permuteBlock g.val.val (support (c0Encoder (p.1.val.val,p.2.val))) at hc
    rw [← coordinatePermutation_support,hr] at hc
    exact ((c0Encoder_contains_tetrad _ _ i).mp hc).2
  have hweight : hammingNorm (c0Encoder (p.1.val.val,r)) = 12 := by
    rw [← hr,coordinatePermutation_weight]
    exact dodecad_size _ (dodecadParametersSupport i p).val.prop
  have hz (k : HexIndex) (hk : p.1.val.val.val k = 0) :
      r.val (hexIndexEquiv k) = p.2.val.val (hexIndexEquiv k) := by
    by_cases hki : k = i
    · subst k; exact hri.trans p.2.prop.1.symm
    · rw [p.2.prop.2 k hki hk]
      exact dodecad_parameters_empty _ r i k hweight p.1.val.prop hri hki hk
  obtain ⟨t,ht⟩ := dodecad_translation_parameters i p.1.val p.1.prop r p.2.val hz
  let x : TetradPointAffine i := SemidirectProduct.inl (Multiplicative.ofAdd t) * SemidirectProduct.inr b
  have hx : x ∈ dodecadAffineStabilizer i p := by
    apply (dodecadAffineStabilizer_mem i p x).mpr
    change coordinatePermutation (tetradPointStabilizerEquiv i x).val.val _ = _
    have he : tetradPointStabilizerEquiv i x =
        tetradPointStabilizerEquiv i (SemidirectProduct.inl (Multiplicative.ofAdd t)) * g :=
      (tetradPointStabilizerEquiv i).map_mul _ _
    rw [he]
    change coordinatePermutation ((affinePermutation t.val.val 1) * g.val.val) _ = _
    rw [coordinatePermutation_mul,hr]
    exact dodecad_translation_word i p.1.val t r p.2.val ht
  exact ⟨⟨x,hx⟩,by simp [x]⟩

theorem dodecadKleinProjection_surjective (i : HexIndex) (p : DodecadParameters i)
    (j : HexIndex) (hji : j ≠ i) (hj : p.1.val.val.val j = 0) :
    Function.Surjective (dodecadKleinProjection i p j hji hj) := by
  intro b
  let h : hexDoubleZero i j := ⟨p.1.val.val,p.1.val.prop,hj⟩
  have hh : h ≠ 0 := fun hz => p.1.prop (Subtype.ext
    (congrArg (fun u : hexDoubleZero i j => u.val) hz))
  have he := congrArg (fun σ : Equiv.Perm {u : hexDoubleZero i j // u ≠ 0} => σ ⟨h,hh⟩) b.prop
  have hb : hexZeroLinear i b.val.val.val p.1.val = p.1.val := by
    apply Subtype.ext
    exact congrArg (fun u : {u : hexDoubleZero i j // u ≠ 0} => u.val.val) he
  obtain ⟨x,hx⟩ := dodecadAffineProjection_lift i p b.val.val hb
  refine ⟨x,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hx

end Atlas.Codes
