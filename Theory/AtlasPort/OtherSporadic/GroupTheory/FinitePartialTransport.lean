/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/FinitePartialTransport.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Finset.Card

/-!
# Matching finite partial permutations

Local point transports fixing a prescribed set extend to finite partial
permutations. Induction adds one point by composing with a transport fixing
the images of the previously matched points.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/FinitePartialTransport.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for downstream calculations.
-/

@[expose] public section

namespace Atlas.GroupTheory

/-- Local point transports fixing at most n prescribed points extend to a
transport matching any partial permutation on at most n+1 points. -/
theorem finite_partial_match {G X : Type*} [Group G] [MulAction G X]
    [DecidableEq X] (R : Subgroup G) (S : Finset X) (n : ℕ)
    (hlocal : ∀ T : Finset X, S ⊆ T → T.card ≤ n → ∀ x y : X,
      x ∉ T → y ∉ T → ∃ r : R, r.val • x=y ∧ ∀ i ∈ T, r.val • i=i)
    (g : G) (hg : ∀ i ∈ S, g • i=i)
    (U : Finset X) (hdis : Disjoint S U) (hcard : (S ∪ U).card ≤ n+1) :
    ∃ r : R, ∀ i ∈ S ∪ U, r.val • i=g • i := by
  classical
  revert hdis hcard
  induction U using Finset.induction_on with
  | empty =>
      intro _ _
      refine ⟨1,?_⟩
      intro i hi
      have hiS : i ∈ S := by simpa using hi
      simpa using (hg i hiS).symm
  | @insert a U ha ih =>
      intro hdis hcard
      have haS : a ∉ S := fun h => Finset.disjoint_left.mp hdis h (by simp)
      have hau : a ∉ S ∪ U := by simpa using And.intro haS ha
      have hjoin : S ∪ insert a U=insert a (S ∪ U) := by ext; simp
      rw [hjoin,Finset.card_insert_of_notMem hau] at hcard
      have hsmall : (S ∪ U).card ≤ n := by omega
      have hdisU : Disjoint S U := Finset.disjoint_left.mpr (fun i hiS hiU =>
        Finset.disjoint_left.mp hdis hiS (Finset.mem_insert_of_mem hiU))
      obtain ⟨r,hr⟩ := ih hdisU (by omega)
      let T := (S ∪ U).image (fun i => g • i)
      have hT : T.card ≤ n := by
        rw [Finset.card_image_of_injective _ (MulAction.injective g)]
        exact hsmall
      have hST : S ⊆ T := by
        intro i hi
        exact Finset.mem_image.mpr ⟨i,Finset.mem_union_left _ hi,hg i hi⟩
      have hx : r.val • a ∉ T := by
        intro h
        obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
        have hie : i=a := (MulAction.injective r.val) ((hr i hi).trans he)
        exact hau (hie ▸ hi)
      have hy : g • a ∉ T := by
        intro h
        obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
        exact hau ((MulAction.injective g he) ▸ hi)
      obtain ⟨t,hta,ht⟩ := hlocal T hST hT (r.val • a) (g • a) hx hy
      refine ⟨t*r,?_⟩
      intro i hi
      change (t.val*r.val) • i = g • i
      rw [mul_smul]
      rw [hjoin] at hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hta
      · rw [hr i hi]
        exact ht _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

end Atlas.GroupTheory
