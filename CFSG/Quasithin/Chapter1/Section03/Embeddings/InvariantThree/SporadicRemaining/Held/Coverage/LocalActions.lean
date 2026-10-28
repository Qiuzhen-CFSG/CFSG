module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Reductions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalSubgroups
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.Residual
public import Theory.SpecificGroups.Held.Automorphisms.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.LocalActions.Reductions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.LocalActions.Exhaustion
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.LocalActions.RepresentativeImages
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Transport

/-!
# Complete pair and action classification under local Held placement

The exhaustive local conjugacy theorem carries both members of the given
pair to one of the two literal representatives by the same element of the
original local overgroup. Restrict this conjugation and compose it with the
certified representative plane coordinates. This constructs the plane without
realization or normalizer assumptions and transfers the complete inner and
extending images, not just actors preserving a chosen local overgroup.

Every inner image is the diagonal four-group. The full image is monomial D8
for the pure representatives (j=0), and diagonal for the mixed representatives
(j=1). The full classification uses only automorphism realization; the allowed
normalizer-quotient bound is unnecessary. Pulling back the diagonal axis in
the actual Frattini quotient supplies a proper nonzero invariant for every
subgroup of the inner image.

Sources: Aschbacher–Smith, printed pp.509–511; GLS3 Table 5.3p. This is the
retained Held branch described in docs/quasithin-proof-basis.md, not the
unmodified Held exclusion of source Proposition 1.3.4. Global pair placement
and the interval-normalizer clause remain with their respective owners.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs.LocalActions

open Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.LocalActions
open Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages
open Held.LocalPairs.PairCoverage.LocalActions.Transport

/-- Restriction of the actual ambient conjugation to a literal odd representative. -/
noncomputable def conjugateOddEquiv (R : Subgroup Held.He) (i : Bool) (j : Fin 2)
    (g : Held.He) (hR : R.map (MulAut.conj g).toMonoidHom = candidateOdd i j) :
    R ≃* candidateOdd i j :=
  ((MulAut.conj g).subgroupMap R).trans (MulEquiv.subgroupCongr hR)

theorem conjugateOddEquiv_apply (R : Subgroup Held.He) (i : Bool) (j : Fin 2)
    (g : Held.He) (hR : R.map (MulAut.conj g).toMonoidHom = candidateOdd i j)
    (x : R) : (conjugateOddEquiv R i j g hR x : Held.He) = MulAut.conj g x := rfl

/-- Plane coordinates pulled back from the representative through the same conjugation. -/
noncomputable def conjugatePlaneEquiv (R : Subgroup Held.He) (i : Bool) (j : Fin 2)
    (g : Held.He) (hR : R.map (MulAut.conj g).toMonoidHom = candidateOdd i j) :
    R ≃* Plane 3 :=
  (conjugateOddEquiv R i j g hR).trans (candidateOddEquiv i j)

/-- Simultaneous conjugacy transports the entire inner image, in the actual coordinates. -/
theorem inner_image_of_conjugate (S R : Subgroup Held.He) (i : Bool) (j : Fin 2)
    (g : Held.He) (hS : S.map (MulAut.conj g).toMonoidHom = candidateTwo i j)
    (hR : R.map (MulAut.conj g).toMonoidHom = candidateOdd i j) :
    ((innerPairAction S R).range).map
      (MulAut.congr (conjugatePlaneEquiv R i j g hR)).toMonoidHom = diagonal := by
  rw [conjugatePlaneEquiv, map_congr_trans]
  have ht := innerRestriction_range_map (MulAut.conj g)
    (membership_of_map_eq _ hS) (membership_of_map_eq _ hR)
    (conjugateOddEquiv R i j g hR) (conjugateOddEquiv_apply R i j g hR)
  change ((innerPairAction S R).range).map
    (MulAut.congr (conjugateOddEquiv R i j g hR)).toMonoidHom =
      (innerPairAction (candidateTwo i j) (candidateOdd i j)).range at ht
  rw [ht]
  exact RepresentativeImages.candidate_innerPairAction_range_map_eq_diagonal i j

/-- Simultaneous conjugacy transports every extending automorphism, including
actors exchanging the local overgroups. -/
theorem full_image_of_conjugate
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (S R : Subgroup Held.He) (i : Bool) (j : Fin 2)
    (g : Held.He) (hS : S.map (MulAut.conj g).toMonoidHom = candidateTwo i j)
    (hR : R.map (MulAut.conj g).toMonoidHom = candidateOdd i j) :
    (pairAutomizer S R).map
      (MulAut.congr (conjugatePlaneEquiv R i j g hR)).toMonoidHom =
        if j = 0 then monomial else diagonal := by
  rw [conjugatePlaneEquiv, map_congr_trans]
  have ht := pairRestriction_range_map (MulAut.conj g)
    (membership_of_map_eq _ hS)
    (conjugateOddEquiv R i j g hR) (conjugateOddEquiv_apply R i j g hR)
  rw [pairRestriction_range, pairRestriction_range] at ht
  rw [ht]
  exact RepresentativeImages.candidate_pairAutomizer_image hrealize i j

/-- Local placement gives an actual elementary plane without any automorphism
realization or normalizer-bound assumption. -/
theorem plane_of_placement
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i) :
    Nonempty (R ≃* Plane 3) := by
  obtain ⟨j, g, _, _, hR⟩ := pair_conjugate i S R h hplace
  exact ⟨conjugatePlaneEquiv R i j g hR⟩

/-- The full inner image of every placed pair is diagonal in explicit
representative coordinates. In particular this needs no realization assumption. -/
theorem inner_coordinates_of_placement
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i) :
    ∃ e : R ≃* Plane 3,
      ((innerPairAction S R).range).map (MulAut.congr e).toMonoidHom = diagonal := by
  obtain ⟨j, g, _, hS, hR⟩ := pair_conjugate i S R h hplace
  exact ⟨conjugatePlaneEquiv R i j g hR, inner_image_of_conjugate S R i j g hS hR⟩

/-- Exhaustive simultaneous representatives and exact full images for a locally
placed source pair. The conjugation belongs to the original local overgroup. -/
theorem pair_images_of_placement
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i) :
    ∃ (j : Fin 2) (g : Held.He), g ∈ localOvergroup i ∧
      (S : Subgroup Held.He).map (MulAut.conj g).toMonoidHom = candidateTwo i j ∧
      ∃ hR : R.map (MulAut.conj g).toMonoidHom = candidateOdd i j,
        ((innerPairAction S R).range).map
            (MulAut.congr (conjugatePlaneEquiv R i j g hR)).toMonoidHom = diagonal ∧
        (pairAutomizer S R).map
            (MulAut.congr (conjugatePlaneEquiv R i j g hR)).toMonoidHom =
          (if j = 0 then monomial else diagonal) ∧
        (planeAction S R (conjugatePlaneEquiv R i j g hR)).range =
          if j = 0 then monomial else diagonal := by
  obtain ⟨j, g, hg, hS, hR⟩ := pair_conjugate i S R h hplace
  have hfull := full_image_of_conjugate hrealize S R i j g hS hR
  refine ⟨j, g, hg, hS, hR, inner_image_of_conjugate S R i j g hS hR, hfull, ?_⟩
  rw [planeAction_range hrealize]
  exact hfull

/-- A convenient image-list interface for the global placement owner. -/
theorem full_action_of_placement
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i) :
    ∃ e : R ≃* Plane 3,
      ((innerPairAction S R).range).map (MulAut.congr e).toMonoidHom = diagonal ∧
      ((planeAction S R e).range = diagonal ∨ (planeAction S R e).range = monomial) := by
  obtain ⟨e, he⟩ := inner_coordinates_of_placement i S R h hplace
  exact ⟨e, he, full_action_of_inner_diagonal hrealize S R e he⟩

/-- Every subgroup of the inner image fixes a proper nonzero subgroup of the
actual Frattini quotient. This is stronger than the needed two-subgroup case. -/
theorem inner_invariant_of_placement
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i)
    (E : Subgroup (MulAut R)) (hE : E ≤ (innerPairAction S R).range) :
    ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ b ∈ E, ∀ x ∈ A, quotientAut (frattini R) b x ∈ A := by
  obtain ⟨e, he⟩ := inner_coordinates_of_placement i S R h hplace
  exact inner_invariant_of_diagonal S R e he.le E hE

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs.LocalActions
