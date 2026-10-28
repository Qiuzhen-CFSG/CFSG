/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/SimpleStabilizerFaithful.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Faithfulness from a simple stabilizer

The action kernel intersects the simple stabilizer trivially unless that stabilizer is normal.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/SimpleStabilizerFaithful.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies are exposed where the downstream stabilizer constructions use reduction.
-/

@[expose] public section

namespace Atlas.GroupTheory
open MulAction

/-- A simple point stabilizer which is not normal forces faithfulness. -/
theorem faithful_of_simple_stabilizer_not_normal {G X : Type*} [Group G]
    [MulAction G X] (a : X) [IsSimpleGroup (stabilizer G a)]
    (hn : ¬ (stabilizer G a).Normal) : FaithfulSMul G X := by
  let K := stabilizer G a
  let f := toPermHom G X
  let N := f.ker
  have hNK : N ≤ K := by
    intro g hg
    have he : f g = 1 := hg
    exact congrArg (fun p : Equiv.Perm X => p a) he
  have hN : N = ⊥ := by
    rcases (inferInstance : (N.subgroupOf K).Normal).eq_bot_or_eq_top with hb | ht
    · apply bot_unique
      intro g hg
      have hm : (⟨g,hNK hg⟩ : K) ∈ N.subgroupOf K := hg
      rw [hb,Subgroup.mem_bot] at hm
      exact congrArg Subtype.val hm
    · exfalso
      apply hn
      have hKN : K ≤ N := by
        intro g hg
        have hm : (⟨g,hg⟩ : K) ∈ N.subgroupOf K := by rw [ht]; trivial
        exact hm
      have he : K = N := le_antisymm hKN hNK
      change K.Normal
      rw [he]
      infer_instance
  constructor
  intro g h hgh
  apply (f.ker_eq_bot_iff.mp hN)
  exact Equiv.ext hgh

end Atlas.GroupTheory
