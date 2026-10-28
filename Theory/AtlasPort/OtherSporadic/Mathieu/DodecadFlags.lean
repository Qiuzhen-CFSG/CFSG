/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadLinearTransport
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24FourTransitive

/-!
# DodecadFlags

Golay automorphisms transport a dodecad together with four ordered interior coordinates.
First normalize the ordered four-set as a tetrad, then use the tetrad pointwise
stabilizer to match the dodecad.

Source: `Atlas/Mathieu/DodecadFlags.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open Finset

theorem dodecad_ordered_flags_transitive (D E : Dodecad) (e f : Fin 4 ↪ Omega)
    (he : ∀ k, e k ∈ D.val) (hf : ∀ k, f k ∈ E.val) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val D.val = E.val ∧
      ∀ k, g.val (e k) = f k := by
  let i : HexIndex := (0,0)
  obtain ⟨a,ha⟩ := orderedFour_to_tetrad e i
  obtain ⟨b,hb⟩ := orderedFour_to_tetrad f i
  have hD : tetrad i ⊆ permuteBlock a.val D.val := by
    intro p hp
    have hi := (mem_tetrad p i).mp hp
    exact mem_image.mpr ⟨e p.2, he p.2, (ha p.2).trans (Prod.ext hi.symm rfl)⟩
  have hE : tetrad i ⊆ permuteBlock b.val E.val := by
    intro p hp
    have hi := (mem_tetrad p i).mp hp
    exact mem_image.mpr ⟨f p.2, hf p.2, (hb p.2).trans (Prod.ext hi.symm rfl)⟩
  let D' : DodecadsThroughTetrad i :=
    ⟨⟨permuteBlock a.val D.val,codePreserving_dodecad_forward _ a.prop _ D.prop⟩,hD⟩
  let E' : DodecadsThroughTetrad i :=
    ⟨⟨permuteBlock b.val E.val,codePreserving_dodecad_forward _ b.prop _ E.prop⟩,hE⟩
  obtain ⟨c,hc⟩ := dodecad_local_transitive i D' E'
  refine ⟨b⁻¹*c.val*a,?_,?_⟩
  · change permuteBlock (b.val⁻¹*c.val.val*a.val) D.val = E.val
    rw [permuteBlock_mul,permuteBlock_mul]
    change permuteBlock b.val⁻¹ (permuteBlock c.val.val D'.val.val) = E.val
    rw [hc]
    change permuteBlock b.val⁻¹ (permuteBlock b.val E.val) = E.val
    rw [← permuteBlock_mul,inv_mul_cancel,permuteBlock_one]
  · intro k
    change b.val⁻¹ (c.val.val (a.val (e k))) = f k
    rw [ha,(tetradPointStabilizer_mem i c.val).mp c.prop k,← hb k]
    exact b.val.symm_apply_apply _

theorem dodecad_four_embedding (D : Dodecad) :
    ∃ e : Fin 4 ↪ Omega, ∀ k, e k ∈ D.val := by
  classical
  have hc : Fintype.card (Fin 4) ≤ Fintype.card D.val := by
    simp only [Fintype.card_fin, Fintype.card_coe, dodecad_size _ D.prop]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  exact ⟨e.trans (Function.Embedding.subtype _),fun k => (e k).prop⟩

theorem dodecad_transitive_explicit (D E : Dodecad) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val D.val = E.val := by
  obtain ⟨e,he⟩ := dodecad_four_embedding D
  obtain ⟨f,hf⟩ := dodecad_four_embedding E
  obtain ⟨g,hg,_⟩ := dodecad_ordered_flags_transitive D E e f he hf
  exact ⟨g,hg⟩

end Atlas.Codes
