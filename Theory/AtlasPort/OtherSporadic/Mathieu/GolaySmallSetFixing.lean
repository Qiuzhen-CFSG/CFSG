/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.GolayOctadTransitivity

/-!
# GolaySmallSetFixing

The pointwise stabilizer of a small coordinate set transports disjoint sets of the same
size when the total size is at most five. Restrict five-transitivity to the stabilizer
action and extend enumerations of the two sets.

Source: `Atlas/Mathieu/GolaySmallSetFixing.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem mathieu24_fixing_small_set_transitive (A S T : Finset Omega) (k : ℕ)
    (hAS : Disjoint A S) (hAT : Disjoint A T) (hS : S.card = k) (hT : T.card = k)
    (hk : A.card + k ≤ 5) :
    ∃ g : Mathieu24CodeModel, (∀ a ∈ A, g.val a = a) ∧ permuteBlock g.val S = T := by
  let := mathieu24_five_transitive
  have ht := SubMulAction.ofFixingSubgroup.isMultiplyPretransitive'
    (G := Mathieu24CodeModel) (m := k) (n := 5) (A : Set Omega)
    (by simpa using hk) (by norm_num [Omega,HexIndex])
  let eS : Fin k ↪ SubMulAction.ofFixingSubgroup Mathieu24CodeModel (A : Set Omega) :=
    ⟨fun i => ⟨finiteSetEmbedding S hS i,by
      have hi : finiteSetEmbedding S hS i ∈ S := (finiteSetLabelling S hS i).prop
      exact fun ha => Finset.disjoint_left.mp hAS ha hi⟩,
      fun i j h => (finiteSetEmbedding S hS).injective
        (congrArg (fun x : SubMulAction.ofFixingSubgroup Mathieu24CodeModel (A : Set Omega) => x.val) h)⟩
  let eT : Fin k ↪ SubMulAction.ofFixingSubgroup Mathieu24CodeModel (A : Set Omega) :=
    ⟨fun i => ⟨finiteSetEmbedding T hT i,by
      have hi : finiteSetEmbedding T hT i ∈ T := (finiteSetLabelling T hT i).prop
      exact fun ha => Finset.disjoint_left.mp hAT ha hi⟩,
      fun i j h => (finiteSetEmbedding T hT).injective
        (congrArg (fun x : SubMulAction.ofFixingSubgroup Mathieu24CodeModel (A : Set Omega) => x.val) h)⟩
  obtain ⟨g,hg⟩ := MulAction.isMultiplyPretransitive_iff.mp ht eS eT
  refine ⟨g.val,?_,?_⟩
  · intro a ha
    exact (mem_fixingSubgroup_iff Mathieu24CodeModel).mp g.prop a ha
  · rw [← finiteSetEmbedding_image S hS,← finiteSetEmbedding_image T hT]
    change (Finset.univ.image (finiteSetEmbedding S hS)).image g.val.val = _
    rw [Finset.image_image]
    apply Finset.image_congr
    intro i _
    exact congrArg Subtype.val (congrArg (fun e => e i) hg)

end Atlas.Codes
