/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TetradMonomialLift

/-!
# SextetCoordinates

Labelling the six parts of an unordered sextet and their four points produces an actual
permutation of Golay coordinates. It carries standard tetrads to the chosen parts, so
their pairwise unions give Golay codewords.

Source: `Atlas/Mathieu/SextetCoordinates.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators
open Finset

def sextetRows (S : UnorderedSextet) (i : HexIndex) : Fin 4 ≃ {p // p ∈ labelSextet S i} := by
  classical
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin,Fintype.card_coe,(labelSextet_valid S).tetrad_size]

/-- Arbitrarily chosen part and row labels; no code preservation is assumed. -/
def sextetCoordinates (S : UnorderedSextet) : Equiv.Perm Omega := Equiv.ofBijective
  (fun p => (sextetRows S p.1 p.2).val) (by
    constructor
    · rintro ⟨i,k⟩ ⟨j,l⟩ he
      dsimp only at he
      have hij : i = j := ((labelSextet_valid S).partition _).unique
        (sextetRows S i k).prop (he.symm ▸ (sextetRows S j l).prop)
      subst j
      have hkl := (sextetRows S i).injective (Subtype.ext he)
      exact Prod.ext rfl hkl
    · intro p
      obtain ⟨i,hi,_⟩ := (labelSextet_valid S).partition p
      obtain ⟨k,hk⟩ := (sextetRows S i).surjective ⟨p,hi⟩
      exact ⟨(i,k),congrArg Subtype.val hk⟩)

theorem sextetCoordinates_tetrad (S : UnorderedSextet) (i : HexIndex) :
    permuteBlock (sextetCoordinates S) (tetrad i) = labelSextet S i := by
  classical
  ext p
  constructor
  · rintro hp
    obtain ⟨⟨j,k⟩,hj,rfl⟩ := mem_image.mp hp
    have hj' : j = i := (mem_tetrad _ _).mp hj
    subst j
    exact (sextetRows S i k).prop
  · intro hp
    obtain ⟨k,hk⟩ := (sextetRows S i).surjective ⟨p,hp⟩
    exact mem_image.mpr ⟨(i,k),(mem_tetrad _ _).mpr rfl,congrArg Subtype.val hk⟩

theorem sextetCoordinates_parts (S : UnorderedSextet) :
    permuteSextetParts (sextetCoordinates S) distinguishedUnorderedSextet.val = S.val := by
  change (univ.image tetrad).image (permuteBlock (sextetCoordinates S)) = S.val
  rw [image_image]
  simp only [Function.comp_def,sextetCoordinates_tetrad]
  exact labelSextet_parts S

theorem wholeTetrad_pair_support (i j : HexIndex) (hij : i ≠ j) :
    support (wholeTetrad i+wholeTetrad j) = tetrad i ∪ tetrad j := by
  classical
  ext p
  simp only [support,mem_filter,mem_univ,true_and,mem_union,mem_tetrad]
  simp only [wholeTetrad,Pi.add_apply,rho,LinearMap.coe_mk,AddHom.coe_mk,Pi.single_apply,
    Equiv.apply_eq_iff_eq]
  by_cases hi : i = p.1
  · subst i
    simp [hij]
  · by_cases hj : j = p.1
    · subst j; simp [Ne.symm hi]
    · simp [Ne.symm hi,Ne.symm hj]

theorem sextetCoordinates_pair_mem (S : UnorderedSextet) (i j : HexIndex) :
    coordinatePermutation (sextetCoordinates S) (wholeTetrad i+wholeTetrad j) ∈ golay := by
  classical
  by_cases hij : i = j
  · subst j; simp [binaryWord_add_self]
  have ho := (labelSextet_valid S).pair_octads i j hij
  obtain ⟨w,_,hw⟩ := (octads_mem _).mp ho
  have hs : support (coordinatePermutation (sextetCoordinates S) (wholeTetrad i+wholeTetrad j)) =
      labelSextet S i ∪ labelSextet S j := by
    rw [coordinatePermutation_support,wholeTetrad_pair_support i j hij]
    simp only [permuteBlock,image_union]
    exact congrArg₂ (· ∪ ·) (sextetCoordinates_tetrad S i) (sextetCoordinates_tetrad S j)
  have he := support_injective (hs.trans hw.symm)
  exact he ▸ w.prop

end Atlas.Codes
