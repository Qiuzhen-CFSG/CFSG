module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.LocalActions.Reductions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.LocalActions.RepresentativeImages.InnerImages
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.LocalActions.RepresentativeImages.PureActors
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
import Mathlib.Tactic.FinCases

/-!
# Exact inner and full actions at the four Held representatives

The imported model module constructs the four actual plane equivalences.
For each mixed representative (j=1), the first marked generator has fixed
letters and the second has none. Thus no pair-preserving permutation induces
the coordinate swap. Full realization transfers this exclusion to all abstract
extending automorphisms. The proved self-normalizer equality for the fixed
two-subgroup discharges the inner-image calculation's remaining premise for
all four pairs. The normalizer of that diagonal image bounds every extending
actor, so the mixed-pair full image is exactly diagonal.

For pure representatives (j=0), the certified quarter-turn actors force the
full image to be monomial. Thus both i values give the monomial D8 image at
j=0 and the diagonal four-group at j=1, in the actual `candidateOddEquiv`
coordinates. Only full realization is used for the complete list; no outer
quotient bound is needed. The original conditional assembly helpers are
preserved, followed by the completed representative results. Universal pair
placement belongs to the parent task. These calculations do not assert the
source's blanket Held exclusion.

Sources: GLS3 Table 5.3p and Aschbacher–Smith, printed pp.509–511; all model
calculations concern the fixed ATLAS HeG1-p2058B0 permutation carrier.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs.LocalActions
namespace RepresentativeImages

open Held.LocalPairs.PairCoverage.LocalActions
open Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages

/-- No preserving permutation can swap the two distinguished axes of a mixed pair. -/
theorem swap_not_mem_mixed_planeAction (i : Bool) :
    swap ∉ (planeAction (candidateTwo i 1) (candidateOdd i 1)
      (candidateOddEquiv i 1)).range := by
  rintro ⟨a, ha⟩
  let r0 : candidateOdd i 1 := ⟨basisGenerator i 1 0, basisGenerator_mem i 1 0⟩
  let r1 : candidateOdd i 1 := ⟨basisGenerator i 1 1, basisGenerator_mem i 1 1⟩
  have he : Held.LocalPairs.permutationPairAction (candidateTwo i 1)
      (candidateOdd i 1) a r0 = r1 := by
    apply (candidateOddEquiv i 1).injective
    rw [← planeAction_apply, ha]
    change swap (candidateOddEquiv i 1
      ⟨basisGenerator i 1 0, basisGenerator_mem i 1 0⟩) =
      candidateOddEquiv i 1 ⟨basisGenerator i 1 1, basisGenerator_mem i 1 1⟩
    rw [candidateOddEquiv_basisGenerator, candidateOddEquiv_basisGenerator]
    funext k
    fin_cases k <;> rfl
  have hp := congrArg (fun x : candidateOdd i 1 => Held.representation x.val) he
  rw [Held.LocalPairs.permutationPairAction_apply] at hp
  exact mixed_axes_not_conjugate i a.val.val hp

/-- Full realization excludes a swap even among abstract extending automorphisms. -/
theorem swap_not_mem_mixed_pairAutomizer
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom) (i : Bool) :
    swap ∉ (pairAutomizer (candidateTwo i 1) (candidateOdd i 1)).map
      (MulAut.congr (candidateOddEquiv i 1)).toMonoidHom := by
  rw [← planeAction_range hrealize]
  exact swap_not_mem_mixed_planeAction i

/-- The mixed-pair full image is diagonal once the actual inner image is known.
The inner-image calculation remains a separate premise to be discharged. -/
theorem mixed_pairAutomizer_eq_diagonal_of_inner
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom) (i : Bool)
    (hinner : ((innerPairAction (candidateTwo i 1) (candidateOdd i 1)).range).map
      (MulAut.congr (candidateOddEquiv i 1)).toMonoidHom = diagonal) :
    (pairAutomizer (candidateTwo i 1) (candidateOdd i 1)).map
      (MulAut.congr (candidateOddEquiv i 1)).toMonoidHom = diagonal := by
  rcases pairAutomizer_of_inner_diagonal _ _ (candidateOddEquiv i 1) hinner with h | h
  · exact h
  · exfalso
    apply swap_not_mem_mixed_pairAutomizer hrealize i
    rw [h]
    exact (show zpowers swap ≤ monomial from le_sup_right) (mem_zpowers _)

theorem mixed_planeAction_eq_diagonal_of_inner
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom) (i : Bool)
    (hinner : ((innerPairAction (candidateTwo i 1) (candidateOdd i 1)).range).map
      (MulAut.congr (candidateOddEquiv i 1)).toMonoidHom = diagonal) :
    (planeAction (candidateTwo i 1) (candidateOdd i 1) (candidateOddEquiv i 1)).range =
      diagonal := by
  rw [planeAction_range hrealize]
  exact mixed_pairAutomizer_eq_diagonal_of_inner hrealize i hinner

/-- An actual non-diagonal preserving permutation forces the full pure-pair
image to be monomial, once its inner image is diagonal. -/
theorem pure_pairAutomizer_eq_monomial_of_inner_and_actor
    (i : Bool)
    (hinner : ((innerPairAction (candidateTwo i 0) (candidateOdd i 0)).range).map
      (MulAut.congr (candidateOddEquiv i 0)).toMonoidHom = diagonal)
    (a : Held.LocalPairs.permutationPairStabilizer (candidateTwo i 0) (candidateOdd i 0))
    (ha : planeAction (candidateTwo i 0) (candidateOdd i 0) (candidateOddEquiv i 0) a
      ∉ diagonal) :
    (pairAutomizer (candidateTwo i 0) (candidateOdd i 0)).map
      (MulAut.congr (candidateOddEquiv i 0)).toMonoidHom = monomial := by
  rcases pairAutomizer_of_inner_diagonal _ _ (candidateOddEquiv i 0) hinner with h | h
  · exfalso
    apply ha
    rw [← h]
    refine ⟨Held.LocalPairs.permutationPairAction _ _ a, ?_, rfl⟩
    exact ⟨Held.permutationGroup.normalizerMonoidHom a.val,
      (mem_automorphismPairStabilizer_iff _ _ _).mp a.property |>.1, fun _ => rfl⟩
  · exact h

/-- The corresponding full permutation-action image, with both finite
calculation premises still explicit. -/
theorem pure_planeAction_eq_monomial_of_inner_and_actor
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom) (i : Bool)
    (hinner : ((innerPairAction (candidateTwo i 0) (candidateOdd i 0)).range).map
      (MulAut.congr (candidateOddEquiv i 0)).toMonoidHom = diagonal)
    (a : Held.LocalPairs.permutationPairStabilizer (candidateTwo i 0) (candidateOdd i 0))
    (ha : planeAction (candidateTwo i 0) (candidateOdd i 0) (candidateOddEquiv i 0) a
      ∉ diagonal) :
    (planeAction (candidateTwo i 0) (candidateOdd i 0) (candidateOddEquiv i 0)).range =
      monomial := by
  rw [planeAction_range hrealize]
  exact pure_pairAutomizer_eq_monomial_of_inner_and_actor i hinner a ha

/-- Every literal representative has the diagonal four-group as its complete
inner restriction image, in the actual marked coordinates. -/
theorem candidate_innerPairAction_range_map_eq_diagonal (i : Bool) (j : Fin 2) :
    ((innerPairAction (candidateTwo i j) (candidateOdd i j)).range).map
      (MulAut.congr (candidateOddEquiv i j)).toMonoidHom = diagonal :=
  innerPairAction_range_map_eq_diagonal
    Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.normalizer_eq i j

/-- The full extending image at either pure representative is the actual
monomial subgroup. The exhibited outer actor supplies the non-diagonal element. -/
theorem pure_pairAutomizer_eq_monomial (i : Bool) :
    (pairAutomizer (candidateTwo i 0) (candidateOdd i 0)).map
      (MulAut.congr (candidateOddEquiv i 0)).toMonoidHom = monomial :=
  pure_pairAutomizer_eq_monomial_of_inner_and_actor i
    (candidate_innerPairAction_range_map_eq_diagonal i 0)
    (PureActors.actor i) (pure_actor_planeAction_not_mem_diagonal i)

/-- The full extending image at either mixed representative is the actual
diagonal subgroup; realization rules out an abstract coordinate swap. -/
theorem mixed_pairAutomizer_eq_diagonal
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom) (i : Bool) :
    (pairAutomizer (candidateTwo i 1) (candidateOdd i 1)).map
      (MulAut.congr (candidateOddEquiv i 1)).toMonoidHom = diagonal :=
  mixed_pairAutomizer_eq_diagonal_of_inner hrealize i
    (candidate_innerPairAction_range_map_eq_diagonal i 1)

/-- All preserving permutation actors at the pure representatives have exactly
the monomial image, including actors that exchange local overgroups. -/
theorem pure_planeAction_eq_monomial
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom) (i : Bool) :
    (planeAction (candidateTwo i 0) (candidateOdd i 0) (candidateOddEquiv i 0)).range =
      monomial := by
  rw [planeAction_range hrealize]
  exact pure_pairAutomizer_eq_monomial i

/-- All preserving permutation actors at the mixed representatives have exactly
the diagonal image. -/
theorem mixed_planeAction_eq_diagonal
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom) (i : Bool) :
    (planeAction (candidateTwo i 1) (candidateOdd i 1) (candidateOddEquiv i 1)).range =
      diagonal := by
  rw [planeAction_range hrealize]
  exact mixed_pairAutomizer_eq_diagonal hrealize i

/-- The exact list of full automizer images in the four certified plane markings. -/
theorem candidate_pairAutomizer_image
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (i : Bool) (j : Fin 2) :
    (pairAutomizer (candidateTwo i j) (candidateOdd i j)).map
      (MulAut.congr (candidateOddEquiv i j)).toMonoidHom =
        if j = 0 then monomial else diagonal := by
  fin_cases j
  · simpa using pure_pairAutomizer_eq_monomial i
  · simpa using mixed_pairAutomizer_eq_diagonal hrealize i

/-- The exact list for the full permutation action, using the same markings. -/
theorem candidate_planeAction_range
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (i : Bool) (j : Fin 2) :
    (planeAction (candidateTwo i j) (candidateOdd i j) (candidateOddEquiv i j)).range =
      if j = 0 then monomial else diagonal := by
  rw [planeAction_range hrealize]
  exact candidate_pairAutomizer_image hrealize i j

/-- The invariant in the actual Frattini quotient required by the outer-actor
reduction, for any subgroup of the inner image at a literal representative. -/
theorem candidate_inner_invariant (i : Bool) (j : Fin 2)
    (E : Subgroup (MulAut (candidateOdd i j)))
    (hE : E ≤ (innerPairAction (candidateTwo i j) (candidateOdd i j)).range) :
    ∃ A : Subgroup (candidateOdd i j ⧸ frattini (candidateOdd i j)), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ b ∈ E, ∀ x ∈ A, quotientAut (frattini (candidateOdd i j)) b x ∈ A :=
  inner_invariant_of_diagonal _ _ (candidateOddEquiv i j)
    (candidate_innerPairAction_range_map_eq_diagonal i j).le E hE


end RepresentativeImages
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs.LocalActions
