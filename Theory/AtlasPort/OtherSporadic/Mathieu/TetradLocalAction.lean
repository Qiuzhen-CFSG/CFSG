/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.HexacodePointAlternating

/-!
# TetradLocalAction

The setwise tetrad stabilizer induces every permutation of its four coordinates.
Surjectivity of the local hexacode action and translations gives all affine plane maps;
unique sextet completion also forces a tetrad stabilizer to preserve its sextet.

Source: `Atlas/Mathieu/TetradLocalAction.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

/-- Every affine permutation of a chosen tetrad is induced by its sextet stabilizer. -/
theorem sextet_tetrad_affine_full (i : HexIndex) (L : KIsometry) (t : K) :
    ∃ s : SextetStabilizer, ∀ k : Fin 4,
      s.val.val (i,k) = (i,rowLabel.symm (L (rowLabel k)+t)) := by
  obtain ⟨a,ha⟩ := hexPointLocal_surjective i L
  obtain ⟨h,hh⟩ := hexCoordinate_surjective i t
  let x : SextetAffineGroup := ⟨Multiplicative.ofAdd h,a.val⟩
  refine ⟨sextetAffineEquiv x,?_⟩
  intro k
  rw [sextetAffineEquiv_coordinates]
  change (a.val.val.perm i,rowLabel.symm
    (a.val.val.localMap (a.val.val.perm i) (rowLabel k)+h.val (a.val.val.perm i))) = _
  rw [hexPointStabilizer_fixed i a]
  change a.val.val.localMap i = L at ha
  change h.val i = t at hh
  rw [ha,hh]

/-- Full S4 restriction, not merely transitivity on the four points. -/
theorem sextet_tetrad_full_symmetric (i : HexIndex) (σ : Equiv.Perm (Fin 4)) :
    ∃ s : SextetStabilizer, ∀ k : Fin 4, s.val.val (i,k) = (i,σ k) := by
  let e : Equiv.Perm K := rowLabel.permCongr σ
  obtain ⟨s,hs⟩ := sextet_tetrad_affine_full i (rowLinearPart e) (e 0)
  refine ⟨s,?_⟩
  intro k
  rw [hs,row_affine_formula]
  apply Prod.ext
  · rfl
  · apply rowLabel.injective
    rw [rowLabel.apply_symm_apply]
    simp [e]

/-- Unique sextet completion identifies the full tetrad stabilizer inside G. -/
theorem tetrad_stabilizer_preserves_sextet (i : HexIndex) (g : Mathieu24CodeModel)
    (hg : permuteBlock g.val (tetrad i) = tetrad i) : g ∈ sextetStabilizer := by
  have ht : tetrad i ∈ distinguishedUnorderedSextet.val := by
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have he : permuteBlock g.val (tetrad i) ∈ (g • distinguishedUnorderedSextet).val :=
    Finset.mem_image.mpr ⟨tetrad i,ht,rfl⟩
  rw [hg] at he
  have h1 := sextet_eq_completion (g • distinguishedUnorderedSextet) ⟨tetrad i,tetrad_card i⟩ he
  have h2 := sextet_eq_completion distinguishedUnorderedSextet ⟨tetrad i,tetrad_card i⟩ ht
  exact h1.trans h2.symm

end Atlas.Codes
