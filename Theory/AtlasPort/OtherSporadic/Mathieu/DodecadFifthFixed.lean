/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadLinearTransport
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeWordPosition

/-!
# DodecadFifthFixed

A tetrad pointwise stabilizer element preserving a dodecad and fixing a fifth point
inside it is the identity. Decoding first forces the linear part, and the mask-kernel
calculation then eliminates the remaining translation.

Source: `Atlas/Mathieu/DodecadFifthFixed.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

 theorem dodecad_parameter_point_nonzero (i : HexIndex) (p : DodecadParameters i)
    (z : Omega) (hz : z ∈ support (c0Encoder (p.1.val.val,p.2.val))) (hzi : z.1 ≠ i) :
    p.1.val.val.val z.1 ≠ 0 := by
  intro he
  have hr := p.2.prop.2 z.1 hzi he
  have hn := (Finset.mem_filter.mp hz).2
  apply hn
  change j (p.1.val.val.val z.1) z.2 + p.2.val.val (hexIndexEquiv z.1) = 0
  simp [he,hr]

theorem dodecad_affine_recovered_fixed (i : HexIndex) (p : DodecadParameters i)
    (x : TetradPointAffine i)
    (hx : coordinatePermutation (affinePermutation x.left.toAdd.val.val x.right.val.val.val)
      (c0Encoder (p.1.val.val,p.2.val)) = c0Encoder (p.1.val.val,p.2.val)) :
    hexZeroLinear i x.right.val p.1.val = p.1.val := by
  let s := sextetAffineEquiv (tetradPointAffineInclusion i x)
  have hw : sextetC0Action s (c0Equiv (p.1.val.val,p.2.val)) = c0Equiv (p.1.val.val,p.2.val) :=
    Subtype.ext hx
  have hr := recoverHex_equivariant s (c0Equiv (p.1.val.val,p.2.val))
  rw [hw,recoverHex_apply] at hr
  dsimp only [s] at hr
  rw [sextetQuotient_affine] at hr
  exact Subtype.ext hr.symm

theorem dodecad_translation_fixed_mask (i : HexIndex) (h t : hexZeroCoordinate i) (r : P6)
    (ht : coordinatePermutation (affinePermutation t.val.val 1) (c0Encoder (h.val,r)) =
      c0Encoder (h.val,r)) : dodecadMaskMap i h t = 0 := by
  have he := affine_encoder_transform t.val.val 1 h.val.val
    (fun k => r.val (hexIndexEquiv k)) 0
  rw [rowEncoder_C0] at he
  change coordinatePermutation (affinePermutation t.val.val 1) (c0Encoder (h.val,r)) = _ at he
  rw [ht] at he
  have hr : rowEncoder h.val.val (fun k => r.val (hexIndexEquiv k)) 0 =
      rowEncoder h.val.val (affineRepetition t.val.val 1 h.val.val
        (fun k => r.val (hexIndexEquiv k)) 0) 0 := by
    simp only [Monomial.act_one,zero_smul,add_zero] at he
    rw [rowEncoder_C0]
    exact he
  have hp := @rowEncoder_injective
    (h.val.val,(fun k => r.val (hexIndexEquiv k)),0)
    (h.val.val,affineRepetition t.val.val 1 h.val.val (fun k => r.val (hexIndexEquiv k)) 0,0) hr
  have hm := (Prod.mk.inj (Prod.mk.inj hp).2).1
  funext k
  have hk := congrFun hm k.val
  change r.val (hexIndexEquiv k.val) = r.val (hexIndexEquiv k.val) +
    polar (h.val.val k.val) (t.val.val k.val) + 0 * _ at hk
  simp only [zero_mul,add_zero] at hk
  exact (add_left_cancel (a := r.val (hexIndexEquiv k.val))
    ((add_zero _).trans hk)).symm

theorem dodecad_tetrad_fifth_fixed (i : HexIndex) (p : DodecadParameters i)
    (g : TetradPointStabilizer i)
    (hg : permuteBlock g.val.val (support (c0Encoder (p.1.val.val,p.2.val))) =
      support (c0Encoder (p.1.val.val,p.2.val)))
    (z : Omega) (hz : z ∈ support (c0Encoder (p.1.val.val,p.2.val)))
    (hzi : z.1 ≠ i) (hgz : g.val.val z = z) : g = 1 := by
  obtain ⟨x,rfl⟩ := (tetradPointStabilizerEquiv i).surjective g
  have hx : coordinatePermutation (affinePermutation x.left.toAdd.val.val x.right.val.val.val)
      (c0Encoder (p.1.val.val,p.2.val)) = c0Encoder (p.1.val.val,p.2.val) := by
    apply support_injective
    exact (coordinatePermutation_support _ _).trans hg
  have hh := dodecad_affine_recovered_fixed i p x hx
  have hk := dodecad_parameter_point_nonzero i p z hz hzi
  have hp : x.right.val.val.val.perm z.1 = z.1 := congrArg Prod.fst hgz
  have hb := hexPointKernel_fixed_word_position i x.right p.1.val p.1.prop hh z.1 hk hp
  have hx' : x = SemidirectProduct.inl x.left := by
    apply SemidirectProduct.ext
    · rfl
    · exact hb
  rw [hx'] at hx hgz ⊢
  change coordinatePermutation (affinePermutation x.left.toAdd.val.val 1)
    (c0Encoder (p.1.val.val,p.2.val)) = c0Encoder (p.1.val.val,p.2.val) at hx
  have hm := dodecad_translation_fixed_mask i p.1.val x.left.toAdd p.2.val hx
  rcases (dodecadMaskMap_kernel i p.1.val p.1.prop x.left.toAdd).mp hm with ht | ht
  · have hl : x.left = 1 := ht
    rw [hl,map_one,map_one]
  · have he := congrArg (fun z : Omega => rowLabel z.2) hgz
    change rowLabel (rowLabel.symm (rowLabel z.2 + x.left.toAdd.val.val z.1)) = rowLabel z.2 at he
    rw [rowLabel.apply_symm_apply,ht] at he
    exact False.elim (hk (add_left_cancel (he.trans (add_zero _).symm)))

end Atlas.Codes
