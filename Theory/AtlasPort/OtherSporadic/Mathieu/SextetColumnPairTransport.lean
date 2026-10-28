/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetTwoPointTransport

/-!
# SextetColumnPairTransport

A prescribed matching of tetrad columns and two marked coordinates is realized in the
sextet stabilizer when the four involved columns are distinct. Extend the column
matching to a permutation and use two-point affine transport.

Source: `Atlas/Mathieu/SextetColumnPairTransport.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem sextet_tetrad_transport (s : SextetStabilizer) (σ : Equiv.Perm HexIndex)
    (hs : ∀ i k, (s.val.val (i,k)).1 = σ i) (i : HexIndex) :
    permuteBlock s.val.val (tetrad i) = tetrad (σ i) := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hqi := (mem_tetrad q i).mp hq
    apply (mem_tetrad _ _).mpr
    exact (hs q.1 q.2).trans (congrArg σ hqi)
  · rw [permuteBlock_card,tetrad_card,tetrad_card]

theorem sextet_column_pair_transport (i j k l : HexIndex) (a b c d : Omega)
    (he : Function.Injective (![i,j,a.1,b.1] : Fin 4 → HexIndex))
    (hf : Function.Injective (![k,l,c.1,d.1] : Fin 4 → HexIndex)) :
    ∃ s : SextetStabilizer,
      permuteBlock s.val.val (tetrad i ∪ tetrad j) = tetrad k ∪ tetrad l ∧
      s.val.val a = c ∧ s.val.val b = d := by
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair _ _ he hf
  have hi : σ i = k := hσ 0
  have hj : σ j = l := hσ 1
  have ha : σ a.1 = c.1 := hσ 2
  have hb : σ b.1 = d.1 := hσ 3
  have hcd : c.1 ≠ d.1 := fun h => (by decide : (2 : Fin 4) ≠ 3) (hf h)
  obtain ⟨s,hs,hsa,hsb⟩ := sextet_two_point_transport σ a b c d hcd ha hb
  refine ⟨s,?_,hsa,hsb⟩
  change (tetrad i ∪ tetrad j).image s.val.val = _
  rw [Finset.image_union]
  exact congrArg₂ (· ∪ ·) ((sextet_tetrad_transport s σ hs i).trans (congrArg tetrad hi))
    ((sextet_tetrad_transport s σ hs j).trans (congrArg tetrad hj))

end Atlas.Codes
