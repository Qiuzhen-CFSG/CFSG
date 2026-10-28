/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/NormalSimpleImage.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Normal subgroups with simple quotient image

A nontrivial normal image is the whole simple quotient; pull it back over the kernel.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/NormalSimpleImage.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies are exposed where the downstream stabilizer constructions use reduction.
-/

@[expose] public section

namespace Atlas.GroupTheory

theorem normal_eq_top_of_simple_image {G M : Type*} [Group G] [Group M] [IsSimpleGroup M]
    (f : G →* M) (hf : Function.Surjective f) (L : Subgroup G) [hL : L.Normal]
    (hk : f.ker ≤ L) (x : G) (hx : x ∈ L) (hfx : f x ≠ 1) : L = ⊤ := by
  have hm := hL.map f hf
  have he : L.map f = ⊤ := by
    rcases hm.eq_bot_or_eq_top with he | he
    · have hh : f x ∈ L.map f := ⟨x,hx,rfl⟩
      rw [he,Subgroup.mem_bot] at hh
      exact (hfx hh).elim
    · exact he
  have hc := Subgroup.comap_map_eq_self hk
  rw [he,Subgroup.comap_top] at hc
  exact hc.symm

end Atlas.GroupTheory
