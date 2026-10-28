/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadAffineStabilizer

/-!
# DodecadProjectionKernel

The kernel of the affine dodecad stabilizer projection has two elements. The explicit
translation condition identifies it with the polar mask kernel, consisting of zero and
the defining hexacode word.

Source: `Atlas/Mathieu/DodecadProjectionKernel.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

theorem dodecad_translation_mem_iff (i : HexIndex) (p : DodecadParameters i)
    (t : hexZeroCoordinate i) :
    SemidirectProduct.inl (Multiplicative.ofAdd t) ∈ dodecadAffineStabilizer i p ↔
      dodecadMaskMap i p.1.val t = 0 := by
  rw [dodecadAffineStabilizer_mem]
  constructor
  · exact dodecad_translation_fixed_mask i p.1.val t p.2.val
  · intro ht
    apply dodecad_translation_word i p.1.val t p.2.val p.2.val
    intro k
    by_cases hk : p.1.val.val.val k = 0
    · simp [hk]
    · have he : polar (p.1.val.val.val k) (t.val.val k) = 0 := congrFun ht ⟨k,hk⟩
      rw [he,add_zero]

theorem dodecadKleinProjection_eq_one (i : HexIndex) (p : DodecadParameters i)
    (j : HexIndex) (hji : j ≠ i) (hj : p.1.val.val.val j = 0)
    (x : dodecadAffineStabilizer i p) :
    dodecadKleinProjection i p j hji hj x = 1 ↔ x.val.right = 1 := by
  constructor
  · intro hx
    exact congrArg (fun b : (hexFiberPermutationHom i j).ker => b.val.val) hx
  · intro hx
    exact Subtype.ext (Subtype.ext hx)

def dodecadProjectionKernelEquiv (i : HexIndex) (p : DodecadParameters i)
    (j : HexIndex) (hji : j ≠ i) (hj : p.1.val.val.val j = 0) :
    (dodecadKleinProjection i p j hji hj).ker ≃*
      Multiplicative (dodecadMaskMap i p.1.val).ker where
  toFun x := Multiplicative.ofAdd ⟨x.val.val.left.toAdd,by
    have hb := (dodecadKleinProjection_eq_one i p j hji hj x.val).mp x.prop
    have he : x.val.val = SemidirectProduct.inl x.val.val.left := by
      apply SemidirectProduct.ext
      · rfl
      · exact hb
    exact (dodecad_translation_mem_iff i p x.val.val.left.toAdd).mp (he ▸ x.val.prop)⟩
  invFun t := ⟨⟨SemidirectProduct.inl (Multiplicative.ofAdd t.toAdd.val),
    (dodecad_translation_mem_iff i p t.toAdd.val).mpr t.toAdd.prop⟩,
      (dodecadKleinProjection_eq_one i p j hji hj _).mpr rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact ((dodecadKleinProjection_eq_one i p j hji hj x.val).mp x.prop).symm
  right_inv t := by apply Subtype.ext; rfl
  map_mul' x y := by
    apply Subtype.ext
    change (x.val.val * y.val.val).left = x.val.val.left * y.val.val.left
    have hb := (dodecadKleinProjection_eq_one i p j hji hj x.val).mp x.prop
    simp [SemidirectProduct.mul_left,hb]

theorem dodecadKleinProjection_kernel_card (i : HexIndex) (p : DodecadParameters i)
    (j : HexIndex) (hji : j ≠ i) (hj : p.1.val.val.val j = 0) :
    Nat.card (dodecadKleinProjection i p j hji hj).ker = 2 := by
  rw [Nat.card_congr (dodecadProjectionKernelEquiv i p j hji hj).toEquiv]
  rw [Nat.card_congr Multiplicative.toAdd]
  exact dodecadMaskMap_kernel_card i p.1.val p.1.prop

end Atlas.Codes
