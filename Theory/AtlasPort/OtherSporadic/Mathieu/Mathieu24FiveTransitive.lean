/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24FourTransitive

/-!
# Mathieu24FiveTransitive

The Golay automorphism group is five-transitive on its coordinates. After matching four
points to a tetrad, transitivity of its pointwise stabilizer on exterior coordinates
matches the fifth.

Source: `Atlas/Mathieu/Mathieu24FiveTransitive.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

/-- The actual pointwise tetrad stabilizer is transitive on its twenty-point complement. -/
theorem tetradPointStabilizer_complement_transitive (i : HexIndex) (x y : Omega)
    (hx : x.1 ≠ i) (hy : y.1 ≠ i) :
    ∃ g : TetradPointStabilizer i, g.val.val x = y := by
  obtain ⟨b,hb⟩ := hexPointKernel_transitive_complement i x.1 y.1 hx hy
  have hp : b.val.val.val.perm x.1 = y.1 := hb
  obtain ⟨h,hh⟩ := hexZeroCoordinate_other_surjective i y.1 (Ne.symm hy)
    (rowLabel y.2 - b.val.val.val.localMap y.1 (rowLabel x.2))
  let z : TetradPointAffine i := ⟨Multiplicative.ofAdd h,b⟩
  refine ⟨tetradPointStabilizerEquiv i z,?_⟩
  change (sextetAffineEquiv (tetradPointAffineInclusion i z)).val.val (x.1,x.2) = y
  rw [sextetAffineEquiv_coordinates]
  change (b.val.val.val.perm x.1,rowLabel.symm
    (b.val.val.val.localMap (b.val.val.val.perm x.1) (rowLabel x.2)+h.val.val (b.val.val.val.perm x.1))) = y
  rw [hp,hh,add_sub_cancel,rowLabel.symm_apply_apply]

def firstFourEmbedding (e : Fin 5 ↪ Omega) : Fin 4 ↪ Omega :=
  ⟨fun k => e k.castSucc,e.injective.comp (Fin.castSucc_injective 4)⟩

theorem orderedFive_last_outside (e : Fin 5 ↪ Omega) (i : HexIndex) (g : Mathieu24CodeModel)
    (hg : ∀ k : Fin 4, g.val (e k.castSucc) = (i,k)) : (g.val (e 4)).1 ≠ i := by
  intro hi
  let k : Fin 4 := (g.val (e 4)).2
  have hp : g.val (e 4) = (i,k) := by apply Prod.ext; exact hi; rfl
  have he : g.val (e 4) = g.val (e k.castSucc) := hp.trans (hg k).symm
  have hk := congrArg Fin.val (e.injective (g.val.injective he))
  have hb := k.isLt
  change 4 = k.val at hk
  omega

theorem mathieu24_five_transitive_explicit (e f : Fin 5 ↪ Omega) :
    ∃ g : Mathieu24CodeModel, ∀ k : Fin 5, g.val (e k) = f k := by
  obtain ⟨a,ha⟩ := orderedFour_to_tetrad (firstFourEmbedding e) (0,0)
  obtain ⟨b,hb⟩ := orderedFour_to_tetrad (firstFourEmbedding f) (0,0)
  have hxa := orderedFive_last_outside e (0,0) a ha
  have hxb := orderedFive_last_outside f (0,0) b hb
  obtain ⟨c,hc⟩ := tetradPointStabilizer_complement_transitive (0,0) (a.val (e 4)) (b.val (f 4)) hxa hxb
  refine ⟨b⁻¹*c.val*a,?_⟩
  intro k
  change b.val⁻¹ (c.val.val (a.val (e k))) = f k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · change b.val⁻¹ (c.val.val (a.val (e 4))) = f 4
    rw [hc,Equiv.Perm.inv_def,Equiv.symm_apply_apply]
  · change b.val⁻¹ (c.val.val (a.val (firstFourEmbedding e j))) = firstFourEmbedding f j
    rw [ha,(tetradPointStabilizer_mem (0,0) c.val).mp c.prop j,← hb j,Equiv.Perm.inv_def,Equiv.symm_apply_apply]

theorem mathieu24_five_transitive : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 5 := by
  apply MulAction.isMultiplyPretransitive_iff.mpr
  intro e f
  obtain ⟨g,hg⟩ := mathieu24_five_transitive_explicit e f
  exact ⟨g,Function.Embedding.ext hg⟩

end Atlas.Codes
