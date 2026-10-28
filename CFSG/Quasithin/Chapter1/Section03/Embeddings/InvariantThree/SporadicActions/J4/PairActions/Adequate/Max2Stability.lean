module

public import Theory.GroupTheory.MaximalSylowAutomorphisms
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.Conjugacy

/-!
# Stability of maximal max2 embeddings

The certified seed normal closure in the actual max2 word subgroup has
centralizer equal to the powers of its distinguished central involution.
This is the local group's center, and it restricts to the center of every
Sylow two-subgroup. Hence it is characteristic in those Sylow subgroups.

For a maximal proper ambient overgroup actually isomorphic to max2, the
general normalizer argument now proves stability under every automorphism
preserving the supplied Sylow subgroup. This uses maximality to identify
the ambient normalizer of the transported center. It does not identify the
literal word subgroup with the full ambient involution centralizer.

Source: Aschbacher–Smith, proof of 1.3.4, printed p.511/PDF p.528;
GLS3 Table 5.3i. The concrete ATLAS provenance and checked conjugation
comparison are in `TwoCoreCentralizer.Generation.Conjugacy`.
-/

public section

open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] Janko4.modelGroup sourceSubgroup localSubgroup sourceSubgroupEquivLocal

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate

/-- The center of the generated max2 carrier is the marked involution line. -/
theorem max2_local_center_eq : center localSubgroup = zpowers subgroupInvolution := by
  apply le_antisymm
  · exact (center_le_centralizer (localNormalClosure : Set localSubgroup)).trans_eq
      localNormalClosure_centralizer_eq_zpowers
  · exact zpowers_le.mpr NormalClosureControl.involution_mem_center

/-- Each local Sylow has precisely the same center as the whole local group. -/
theorem max2_local_sylow_center_eq (P : Sylow 2 localSubgroup) :
    (center localSubgroup).subgroupOf P.toSubgroup = center P := by
  apply center_subgroupOf_sylow_eq_of_centralizer_le_center
    localNormalClosure localNormalClosure_isPGroup
  rw [localNormalClosure_centralizer_eq_zpowers, max2_local_center_eq]

/-- Maximal max2 embeddings are stable under every Sylow-preserving actor. -/
theorem max2_stable [Finite Janko4.Model] [IsSimpleGroup Janko4.Model]
    (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model)
    (hM : IsCoatom M) (hSM : S.toSubgroup ≤ M) (e : M ≃* sourceSubgroup)
    (b : MulAut Janko4.Model) (hb : ∀ x, b x ∈ S ↔ x ∈ S) :
    ∀ x, b x ∈ M ↔ x ∈ M := by
  have hne : center localSubgroup ≠ ⊥ := by
    intro h
    have hz := NormalClosureControl.involution_mem_center
    rw [h, mem_bot] at hz
    have ho := orderOf_subgroupInvolution
    rw [hz, orderOf_one] at ho
    exact (by decide : (1 : ℕ) ≠ 2) ho
  have hp : IsPGroup 2 (center localSubgroup) := by
    rw [max2_local_center_eq]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_subgroupInvolution]; rfl)
  exact stable_coatom_of_sylow_characteristic_normal (center localSubgroup) hne hp
    (fun P => by rw [max2_local_sylow_center_eq]; infer_instance) S M hM hSM
    (e.trans sourceSubgroupEquivLocal) b hb

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate
