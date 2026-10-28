/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetRecovery

/-!
# SextetTrio

Preserving the distinguished trio under a sextet-stabilizer element is equivalent to
preserving its pairing of columns. Injectivity of taking the union of complete columns
translates the coordinate condition into the column action.

Source: `Atlas/Mathieu/SextetTrio.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open Finset

def pairedColumns (i : Fin 3) : Finset HexIndex := {(i,0),(i,1)}
def columnPairing : Finset (Finset HexIndex) := univ.image pairedColumns
def distinguishedUnorderedTrio : Finset (Finset Omega) := univ.image distinguishedTrio

def columnUnion (U : Finset HexIndex) : Finset Omega := univ.filter (fun p => p.1 ∈ U)

@[simp] theorem mem_columnUnion (U : Finset HexIndex) (p : Omega) :
    p ∈ columnUnion U ↔ p.1 ∈ U := by simp [columnUnion]

theorem columnUnion_injective : Function.Injective columnUnion := by
  intro U V h
  ext i
  have hh := Finset.ext_iff.mp h (i,0)
  simpa only [mem_columnUnion] using hh

theorem columnUnion_pair (i : Fin 3) : columnUnion (pairedColumns i) = distinguishedTrio i := by
  ext p
  simp only [mem_columnUnion,pairedColumns,mem_insert,mem_singleton,
    distinguishedTrio,mem_union,mem_tetrad]

theorem trio_columnUnion : distinguishedUnorderedTrio = columnPairing.image columnUnion := by
  simp only [distinguishedUnorderedTrio,columnPairing,image_image,Function.comp_def,columnUnion_pair]

theorem affine_columnUnion (t : HexWord) (g : Monomial HexIndex) (U : Finset HexIndex) :
    permuteBlock (affinePermutation t g) (columnUnion U) = columnUnion (U.image g.perm) := by
  ext p
  simp only [permuteBlock,mem_image,mem_columnUnion]
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact ⟨q.1,hq,rfl⟩
  · rintro ⟨i,hi,hp⟩
    refine ⟨(affinePermutation t g)⁻¹ p,?_,by simp⟩
    change g.perm.symm p.1 ∈ U
    rw [← hp,g.perm.symm_apply_apply]
    exact hi

theorem affine_trio_iff_pairing (t : HexWord) (g : Monomial HexIndex) :
    distinguishedUnorderedTrio.image (permuteBlock (affinePermutation t g)) =
      distinguishedUnorderedTrio ↔
    columnPairing.image (fun U => U.image g.perm) = columnPairing := by
  rw [trio_columnUnion,image_image]
  have he : (fun U => permuteBlock (affinePermutation t g) (columnUnion U)) =
      fun U => columnUnion (U.image g.perm) := by
    funext U; exact affine_columnUnion t g U
  dsimp only [Function.comp_def]
  rw [he]
  change columnPairing.image (columnUnion ∘ (fun U => U.image g.perm)) =
    columnPairing.image columnUnion ↔ _
  rw [← image_image]
  exact Finset.image_inj columnUnion_injective

theorem sextet_trio_iff_pairing (s : SextetStabilizer) :
    distinguishedUnorderedTrio.image (permuteBlock s.val.val) = distinguishedUnorderedTrio ↔
      columnPairing.image (fun U => U.image (hexCoordinateHom (sextetQuotient s))) =
        columnPairing := by
  obtain ⟨x,rfl⟩ := sextetAffineEquiv.surjective s
  rw [sextetQuotient_affine]
  exact affine_trio_iff_pairing x.left.toAdd.val x.right.val

end Atlas.Codes
