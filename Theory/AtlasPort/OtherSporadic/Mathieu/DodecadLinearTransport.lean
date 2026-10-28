/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadTranslations
public import Theory.AtlasPort.OtherSporadic.Codes.DodecadParameterCount
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeKernelTransitivity

/-!
# DodecadLinearTransport

The tetrad pointwise stabilizer is transitive on dodecads containing that tetrad. A
linear kernel element matches the nonzero hexacode parameters, and an admissible
translation then matches their masks.

Source: `Atlas/Mathieu/DodecadLinearTransport.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

theorem dodecad_linear_word (i : HexIndex) (h : hexZeroCoordinate i) (r : P6)
    (b : hexPointKernel i) :
    ∃ s : P6, coordinatePermutation
      (tetradPointStabilizerEquiv i (SemidirectProduct.inr b)).val.val (c0Encoder (h.val,r)) =
      c0Encoder ((hexZeroLinear i b.val h).val,s) := by
  let x : SextetAffineGroup := tetradPointAffineInclusion i (SemidirectProduct.inr b)
  let w : C0 := sextetC0Action (sextetAffineEquiv x) (c0Equiv (h.val,r))
  obtain ⟨⟨k,s⟩,he⟩ := c0Equiv.surjective w
  have hk : k = (hexZeroLinear i b.val h).val := by
    have hr := recoverHex_equivariant (sextetAffineEquiv x) (c0Equiv (h.val,r))
    rw [recoverHex_apply,sextetQuotient_affine] at hr
    have he' := congrArg recoverHex he
    rw [recoverHex_apply] at he'
    exact he'.trans hr
  refine ⟨s,?_⟩
  have hw := congrArg (fun z : C0 => z.val) he
  rw [hk] at hw
  exact hw.symm

theorem tetrad_fix_preserves_containment (i : HexIndex) (g : TetradPointStabilizer i)
    (D : Finset Omega) (hD : tetrad i ⊆ D) : tetrad i ⊆ permuteBlock g.val.val D := by
  intro p hp
  have hg : g.val.val p = p := g.prop ⟨p,hp⟩
  exact Finset.mem_image.mpr ⟨p,hD hp,hg⟩

theorem dodecad_local_transitive (i : HexIndex) (D E : DodecadsThroughTetrad i) :
    ∃ g : TetradPointStabilizer i, permuteBlock g.val.val D.val.val = E.val.val := by
  obtain ⟨p,rfl⟩ := (dodecadParametersSupport_bijective i).2 D
  obtain ⟨q,rfl⟩ := (dodecadParametersSupport_bijective i).2 E
  obtain ⟨b,hb⟩ := hexPointKernel_nonzero_transitive i p.1.val q.1.val p.1.prop q.1.prop
  let g := tetradPointStabilizerEquiv i (SemidirectProduct.inr b)
  obtain ⟨r,hr⟩ := dodecad_linear_word i p.1.val p.2.val b
  rw [hb] at hr
  have hp := (dodecadParametersSupport i p).prop
  have hri : r.val (hexIndexEquiv i) = 1 := by
    have hc := tetrad_fix_preserves_containment i g _ hp
    change tetrad i ⊆ permuteBlock g.val.val (support (c0Encoder (p.1.val.val,p.2.val))) at hc
    rw [← coordinatePermutation_support,hr] at hc
    exact ((c0Encoder_contains_tetrad _ _ i).mp hc).2
  have hweight : hammingNorm (c0Encoder (q.1.val.val,r)) = 12 := by
    rw [← hr,coordinatePermutation_weight]
    exact dodecad_size _ (dodecadParametersSupport i p).val.prop
  have hz (k : HexIndex) (hk : q.1.val.val.val k = 0) :
      r.val (hexIndexEquiv k) = q.2.val.val (hexIndexEquiv k) := by
    by_cases hki : k = i
    · subst k
      exact hri.trans q.2.prop.1.symm
    · rw [q.2.prop.2 k hki hk]
      exact dodecad_parameters_empty _ r i k hweight q.1.val.prop hri hki hk
  obtain ⟨t,ht⟩ := dodecad_translation_actual i q.1.val q.1.prop r q.2.val hz
  refine ⟨t*g,?_⟩
  change permuteBlock (t.val.val*g.val.val)
    (support (c0Encoder (p.1.val.val,p.2.val))) = support (c0Encoder (q.1.val.val,q.2.val))
  rw [← coordinatePermutation_support,coordinatePermutation_mul,hr,ht]

end Atlas.Codes
