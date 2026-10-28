/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetRecovery

/-!
# SextetMarkings

Affine monomial maps transport the Kleinian markings of a sextet with an explicit half-
pair swap. The local polar identity determines the swap and proves compatibility between
coordinate transport and the transformed marking.

Source: `Atlas/Mathieu/SextetMarkings.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open Finset

def transformedMarking (g : Monomial HexIndex) (m : KleinianMarking) : KleinianMarking :=
  ⟨Monomial.act g m.val,fun i => fun h => m.prop (g.perm.symm i) ((g.localMap i).map_eq_zero_iff.mp h)⟩

def markingHalfSwap (b : Bit) : Equiv.Perm (Fin 2) :=
  if b = 0 then 1 else Equiv.swap 0 1

theorem markingHalfSwap_test : ∀ (b v : Bit) (s : Fin 2),
    (if markingHalfSwap b s = 0 then v+b = 1 else v+b = 0) ↔
      (if s = 0 then v = 1 else v = 0) := by decide

theorem affine_letterPair (L : KIsometry) (t u : K) (s : Fin 2) (k : Fin 4) :
    rowLabel.symm (L (rowLabel k)+t) ∈
      letterPair (L u) (markingHalfSwap (polar (L u) t) s) ↔ k ∈ letterPair u s := by
  simp only [letterPair,mem_filter,mem_univ,true_and,j_row_polar,
    rowLabel.apply_symm_apply,map_add,KIsometry.map_polar]
  exact markingHalfSwap_test _ _ _

theorem affine_markedPair (t : HexWord) (g : Monomial HexIndex)
    (m : KleinianMarking) (i : HexIndex) (s : Fin 2) :
    permuteBlock (affinePermutation t g) (markedPair m (i,s)) =
      markedPair (transformedMarking g m)
        (g.perm i,markingHalfSwap (polar (g.localMap (g.perm i) (m.val i)) (t (g.perm i))) s) := by
  ext p
  simp only [permuteBlock,mem_image]
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨hi,hk⟩ := (markedPair_mem m (i,s) q).mp hq
    rcases q with ⟨j,k⟩
    dsimp only at hi
    subst j
    apply (markedPair_mem _ _ _).mpr
    refine ⟨rfl,?_⟩
    change rowLabel.symm (g.localMap (g.perm i) (rowLabel k)+t (g.perm i)) ∈ _
    simpa only [transformedMarking,Monomial.act_apply,g.perm.symm_apply_apply] using
      (affine_letterPair (g.localMap (g.perm i)) (t (g.perm i)) (m.val i) s k).mpr hk
  · intro hp
    obtain ⟨hi,hk⟩ := (markedPair_mem _ _ p).mp hp
    refine ⟨(affinePermutation t g)⁻¹ p,?_,by simp⟩
    apply (markedPair_mem _ _ _).mpr
    refine ⟨?_,?_⟩
    · change g.perm.symm p.1 = i
      rw [hi,g.perm.symm_apply_apply]
    · change rowLabel.symm ((g.localMap p.1).symm (rowLabel p.2-t p.1)) ∈ letterPair (m.val i) s
      rw [hi]
      apply (affine_letterPair (g.localMap (g.perm i)) (t (g.perm i)) (m.val i) s _).mp
      simpa only [rowLabel.apply_symm_apply,LinearEquiv.apply_symm_apply,
        sub_add_cancel,rowLabel.symm_apply_apply,transformedMarking,Monomial.act_apply,
        g.perm.symm_apply_apply] using hk

theorem sextet_marking_compatibility (x : SextetAffineGroup) (m : KleinianMarking)
    (i : HexIndex) :
    ∃ e : Equiv.Perm (Fin 2), ∀ s,
      permuteBlock (sextetAffineEquiv x).val.val (markedPair m (i,s)) =
        markedPair (transformedMarking x.right.val m) (x.right.val.perm i,e s) := by
  exact ⟨markingHalfSwap (polar (x.right.val.localMap (x.right.val.perm i) (m.val i))
    (x.left.toAdd.val (x.right.val.perm i))),affine_markedPair _ _ _ i⟩

end Atlas.Codes
