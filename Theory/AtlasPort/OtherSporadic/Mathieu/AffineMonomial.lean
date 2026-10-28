/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.AffineRows
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetAction

/-!
# AffineMonomial

Affine monomial maps give actual permutations of the twenty-four Golay coordinates.
Their coordinate formula proves the semidirect multiplication rule, uniqueness of
parameters, and preservation of the tetrad partition.

Source: `Atlas/Mathieu/AffineMonomial.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes
open Finset

/-- An arbitrary affine permutation of the six tetrads, in destination convention. -/
def affinePermutation (t : HexWord) (g : Monomial HexIndex) : Equiv.Perm Omega where
  toFun p := (g.perm p.1,rowLabel.symm (g.localMap (g.perm p.1) (rowLabel p.2) + t (g.perm p.1)))
  invFun p := (g.perm.symm p.1,rowLabel.symm ((g.localMap p.1).symm (rowLabel p.2 - t p.1)))
  left_inv := by intro p; apply Prod.ext <;> simp
  right_inv := by intro p; apply Prod.ext <;> simp

@[simp] theorem affinePermutation_apply (t : HexWord) (g : Monomial HexIndex) (i : HexIndex) (k : Fin 4) :
    affinePermutation t g (i,k) =
      (g.perm i,rowLabel.symm (g.localMap (g.perm i) (rowLabel k) + t (g.perm i))) := rfl

@[simp] theorem affinePermutation_inv_apply (t : HexWord) (g : Monomial HexIndex) (i : HexIndex) (k : Fin 4) :
    (affinePermutation t g)⁻¹ (i,k) =
      (g.perm.symm i,rowLabel.symm ((g.localMap i).symm (rowLabel k - t i))) := rfl

@[simp] theorem affinePermutation_zero_one : affinePermutation 0 1 = 1 := by
  apply Equiv.ext
  intro p
  apply Prod.ext <;> simp [affinePermutation]

theorem affinePermutation_mul (t u : HexWord) (g h : Monomial HexIndex) :
    affinePermutation t g * affinePermutation u h =
      affinePermutation (t + Monomial.act g u) (g*h) := by
  apply Equiv.ext
  intro p
  apply Prod.ext
  · rfl
  · simp [affinePermutation,Monomial.act_apply,Equiv.Perm.mul_def,
      map_add,add_assoc,add_comm]

theorem affinePermutation_injective : Function.Injective
    (fun x : HexWord × Monomial HexIndex => affinePermutation x.1 x.2) := by
  rintro ⟨t,g⟩ ⟨u,h⟩ he
  have hp : g.perm = h.perm := by
    apply Equiv.ext
    intro i
    exact congrArg Prod.fst (Equiv.congr_fun he (i,0))
  have ht : t = u := by
    funext j
    obtain ⟨i,rfl⟩ := g.perm.surjective j
    have hh := congrArg (fun p : Omega => rowLabel p.2) (Equiv.congr_fun he (i,0))
    have hzero : rowLabel 0 = 0 := rfl
    simpa only [affinePermutation,Equiv.coe_fn_mk,Equiv.apply_symm_apply,hzero,
      map_zero,zero_add,hp] using hh
  have hL : g.localMap = h.localMap := by
    funext j
    obtain ⟨i,rfl⟩ := g.perm.surjective j
    apply LinearEquiv.ext
    intro z
    obtain ⟨k,rfl⟩ := rowLabel.surjective z
    have hh := congrArg (fun p : Omega => rowLabel p.2) (Equiv.congr_fun he (i,k))
    simp only [affinePermutation,Equiv.coe_fn_mk,Equiv.apply_symm_apply,hp,ht] at hh
    rw [hp]
    exact add_right_cancel hh
  exact Prod.ext ht (Monomial.ext hp hL)

theorem affinePermutation_tetrad (t : HexWord) (g : Monomial HexIndex) (i : HexIndex) :
    permuteBlock (affinePermutation t g) (tetrad i) = tetrad (g.perm i) := by
  classical
  ext p
  simp only [permuteBlock,mem_image,mem_tetrad]
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact congrArg g.perm hq
  · intro hp
    refine ⟨(affinePermutation t g)⁻¹ p,?_,by simp⟩
    change g.perm.symm p.1 = i
    rw [hp,g.perm.symm_apply_apply]

theorem affinePermutation_preserves_parts (t : HexWord) (g : Monomial HexIndex) :
    permuteSextetParts (affinePermutation t g) distinguishedUnorderedSextet.val =
      distinguishedUnorderedSextet.val := by
  classical
  change (univ.image tetrad).image (permuteBlock (affinePermutation t g)) = univ.image tetrad
  rw [image_image]
  have hh : (fun i => permuteBlock (affinePermutation t g) (tetrad i)) = tetrad ∘ g.perm := by
    funext i; exact affinePermutation_tetrad t g i
  dsimp only [Function.comp_def]
  rw [hh]
  exact labelledSextetParts_relabel tetrad g.perm

end Atlas.Codes
