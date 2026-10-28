/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/LocalFusionFaithfulness.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Faithfulness from local fusion

Rigidity of local normal subgroups and an element fusing outside the local normal subgroup eliminate the global action kernel.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/LocalFusionFaithfulness.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

namespace Atlas.GroupTheory
open MulAction

/-- A normal subgroup containing the local normal subgroup also contains the
whole local group, provided one of its elements fuses outside that subgroup. -/
theorem range_le_normal_of_local_fusion {G H : Type*} [Group G] [Group H]
    (i : H →* G) (E : Subgroup H)
    (hnormal : ∀ N : Subgroup H, N.Normal → N = ⊥ ∨ N = E ∨ N = ⊤)
    (e h : H) (he : e ∈ E) (hh : h ∉ E) (a : G)
    (hfuse : a * i e * a⁻¹ = i h) (L : Subgroup G) [L.Normal]
    (hE : E ≤ L.comap i) : i.range ≤ L := by
  have hhL : h ∈ L.comap i := by
    change i h ∈ L
    rw [← hfuse]
    exact (inferInstance : L.Normal).conj_mem (i e) (hE he) a
  have htop : L.comap i = ⊤ := by
    rcases hnormal (L.comap i) inferInstance with hn | hn | hn
    · have heq : h = 1 := by rwa [hn] at hhL
      exact False.elim (hh (heq.symm ▸ E.one_mem))
    · exact False.elim (hh (hn ▸ hhL))
    · exact hn
  rintro g ⟨k, rfl⟩
  change k ∈ L.comap i
  rw [htop]
  trivial

/-- Local normal-subgroup rigidity and one fusion outside the local normal
subgroup force the global action kernel to vanish. Transitivity is not assumed. -/
theorem action_kernel_eq_bot_of_local_fusion {G H X : Type*} [Group G] [Group H]
    [MulAction G X] (i : H →* G) (x : X)
    (hi : i.range = stabilizer G x) (E : Subgroup H)
    (hnormal : ∀ N : Subgroup H, N.Normal → N = ⊥ ∨ N = E ∨ N = ⊤)
    (e h : H) (he : e ∈ E) (hh : h ∉ E) (a : G)
    (hfuse : a * i e * a⁻¹ = i h)
    (y : X) (k : H) (hmoves : i k • y ≠ y) :
    (toPermHom G X).ker = ⊥ := by
  let K := (toPermHom G X).ker
  let L := K.comap i
  have hL : L.Normal := inferInstance
  have hbot : L = ⊥ := by
    rcases hnormal L hL with hl | hl | hl
    · exact hl
    · have hie : i e ∈ K := by change e ∈ L; rwa [hl]
      have hih : i h ∈ K := hfuse ▸ (inferInstance : K.Normal).conj_mem (i e) hie a
      exact False.elim (hh (hl ▸ (show h ∈ L from hih)))
    · have hik : i k ∈ K := by change k ∈ L; rw [hl]; trivial
      have heq : toPermHom G X (i k) = 1 := hik
      exact False.elim (hmoves (congrArg (fun p : Equiv.Perm X => p y) heq))
  apply le_antisymm _ bot_le
  intro g hg
  have hfix : g ∈ stabilizer G x := by
    have heq : toPermHom G X g = 1 := hg
    exact congrArg (fun p : Equiv.Perm X => p x) heq
  obtain ⟨h, rfl⟩ := hi.symm ▸ hfix
  have heq : h = 1 := by
    have hm : h ∈ L := hg
    rwa [hbot] at hm
  simpa only [heq, map_one] using (show (1 : G) ∈ (⊥ : Subgroup G) from rfl)

end Atlas.GroupTheory
