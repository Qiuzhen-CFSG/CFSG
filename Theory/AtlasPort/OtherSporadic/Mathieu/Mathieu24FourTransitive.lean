/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.TetradPointwiseStabilizer
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Mathieu24FourTransitive

Every ordered four-set of Golay coordinates can be transported to a standard tetrad.
Sextet completion and reconstruction transport the underlying set, then the full
symmetric tetrad action matches the order.

Source: `Atlas/Mathieu/Mathieu24FourTransitive.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open Finset

/-- Every four-subset can be moved to any distinguished tetrad. -/
theorem fourSet_to_tetrad (T : FourSet) (i : HexIndex) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val T.val = tetrad i := by
  classical
  obtain ⟨g,hg⟩ := sextet_equivalent_distinguished (sextetCompletion T)
  have ht : permuteBlock g.val T.val ∈ (g • sextetCompletion T).val :=
    mem_image.mpr ⟨T.val,tetrad_mem_completion T,rfl⟩
  rw [hg] at ht
  obtain ⟨j,_,hj⟩ := mem_image.mp ht
  obtain ⟨a,ha⟩ := hexCoordinateHom_surjective (Equiv.swap j i)
  let s := sextetSection a
  refine ⟨s.val*g,?_⟩
  rw [show (s.val*g).val = s.val.val*g.val from rfl,permuteBlock_mul,← hj]
  change permuteBlock (affinePermutation 0 a.val) (tetrad j) = tetrad i
  rw [affinePermutation_tetrad]
  have hp : a.val.perm j = i := (DFunLike.congr_fun ha j).trans (Equiv.swap_apply_left j i)
  rw [hp]

/-- Normalizing an ordered tetrad uses the full local S4, in addition to four-homogeneity. -/
theorem orderedFour_to_tetrad (e : Fin 4 ↪ Omega) (i : HexIndex) :
    ∃ g : Mathieu24CodeModel, ∀ k : Fin 4, g.val (e k) = (i,k) := by
  classical
  let T : FourSet := ⟨univ.image e,by rw [card_image_of_injective _ e.injective]; simp⟩
  obtain ⟨g,hg⟩ := fourSet_to_tetrad T i
  have hi (k : Fin 4) : (g.val (e k)).1 = i := by
    apply (mem_tetrad _ _).mp
    rw [← hg]
    exact mem_image.mpr ⟨e k,mem_image.mpr ⟨k,mem_univ _,rfl⟩,rfl⟩
  let f : Fin 4 → Fin 4 := fun k => (g.val (e k)).2
  have hf : Function.Injective f := by
    intro k l he
    apply e.injective
    apply g.val.injective
    exact Prod.ext ((hi k).trans (hi l).symm) he
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩
  obtain ⟨s,hs⟩ := sextet_tetrad_full_symmetric i σ⁻¹
  refine ⟨s.val*g,?_⟩
  intro k
  change s.val.val (g.val (e k)) = (i,k)
  have he : g.val (e k) = (i,σ k) := Prod.ext (hi k) rfl
  rw [he,hs,Equiv.Perm.inv_def,Equiv.symm_apply_apply]

theorem mathieu24_four_transitive_explicit (e f : Fin 4 ↪ Omega) :
    ∃ g : Mathieu24CodeModel, ∀ k : Fin 4, g.val (e k) = f k := by
  obtain ⟨a,ha⟩ := orderedFour_to_tetrad e (0,0)
  obtain ⟨b,hb⟩ := orderedFour_to_tetrad f (0,0)
  refine ⟨b⁻¹*a,?_⟩
  intro k
  change b.val⁻¹ (a.val (e k)) = f k
  rw [ha,← hb k,Equiv.Perm.inv_def,Equiv.symm_apply_apply]

theorem mathieu24_four_transitive : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 4 := by
  apply MulAction.isMultiplyPretransitive_iff.mpr
  intro e f
  obtain ⟨g,hg⟩ := mathieu24_four_transitive_explicit e f
  exact ⟨g,Function.Embedding.ext hg⟩

end Atlas.Codes
