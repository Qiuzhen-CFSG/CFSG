/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/ConnectedInvolutionPairs.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Generation by adjacent involution products

Products of endpoint involutions telescope along walks in a connected graph.
This identifies pair-product generation with generation along graph edges.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/ConnectedInvolutionPairs.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for downstream calculations.
-/

@[expose] public section

noncomputable section
namespace Atlas.Algebra

/-- Along any graph walk, products of endpoint involutions telescope into
products attached to edges. No group order or finite graph is needed. -/
theorem connected_involution_pairs_generate {G I : Type*} [Group G]
    (s : I → G) (hs : ∀ i, s i * s i=1) (Γ : SimpleGraph I) (hΓ : Γ.Connected) :
    Subgroup.closure (Set.range (fun ij : I × I => s ij.1 * s ij.2)) =
      Subgroup.closure {g : G | ∃ i j, Γ.Adj i j ∧ g=s i * s j} := by
  let H : Subgroup G := Subgroup.closure {g : G | ∃ i j, Γ.Adj i j ∧ g=s i * s j}
  have hp (i j : I) : s i * s j ∈ H := by
    obtain ⟨w⟩ := hΓ i j
    induction w with
    | nil => rw [hs]; exact H.one_mem
    | @cons i j k hij w ih =>
      have he : s i * s j ∈ H := Subgroup.subset_closure ⟨i,j,hij,rfl⟩
      have hm := H.mul_mem he ih
      have hc : (s i * s j) * (s j * s k)=s i * s k := by
        rw [mul_assoc,← mul_assoc (s j) (s j) (s k),hs,one_mul]
      rw [hc] at hm
      exact hm
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨⟨i,j⟩,rfl⟩
    exact hp i j
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨i,j,_,rfl⟩
    exact Subgroup.subset_closure ⟨(i,j),rfl⟩

/-- Transport the standard internal generation statement along an actual
subgroup equality, keeping all subgroup membership proofs intrinsic. -/
theorem subgroup_preimage_generates_of_closure_eq {G : Type*} [Group G]
    (H : Subgroup G) (S : Set G) (h : Subgroup.closure S=H) :
    Subgroup.closure (H.subtype ⁻¹' S)=⊤ := by
  subst H
  exact Subgroup.closure_preimage_eq_top S

end Atlas.Algebra

