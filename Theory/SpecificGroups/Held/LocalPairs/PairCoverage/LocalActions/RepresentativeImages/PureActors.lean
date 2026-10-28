module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Planes
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors.Checks0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors.Checks1

/-!
# Actual non-diagonal actors at the two pure Held pairs

Each displayed permutation is a checked word in the fixed Held generators
and a certified outer implementer. Its conjugates of all four two-generators
and both marked odd generators preserve the literal candidate subgroups.
Restriction to the genuine plane coordinates gives a quarter-turn for false
and its inverse for true. Both actions escape the diagonal subgroup.

The construction uses the full permutation pair stabilizer, without requiring
preservation of a chosen local overgroup. It needs no realization, quotient
bound, inner-image equality, inner-normalizer calculation or pair coverage.
These lower witnesses feed the separate full-image assembly.

Sources: unchanged ATLAS HeG1-p2058B0 carrier and HeG1-a2W1 implementer;
GLS3 Table 5.3p; Aschbacher–Smith, printed pp.509–511. Discovery provenance
and reproducible certificates are documented in PureActors/source/README.md.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
open Subgroup

/-- The retained left-action permutation; no second GAP inversion occurs. -/
def permutation (i : Bool) : Equiv.Perm (Fin 2058) := if i then Actor1.perm else Actor0.perm

theorem permutation_mem_normalizer (i : Bool) :
    permutation i ∈ normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) := by
  cases i
  · exact Actor0.perm_mem_normalizer
  · exact Actor1.perm_mem_normalizer

theorem permutation_normalizes_two (i : Bool) :
    permutation i ∈ normalizer ((candidateTwo i 0).map representation :
      Set (Equiv.Perm (Fin 2058))) := by
  cases i
  · exact Actor0.perm_normalizes_two
  · exact Actor1.perm_normalizes_two

theorem permutation_normalizes_odd (i : Bool) :
    permutation i ∈ normalizer ((candidateOdd i 0).map representation :
      Set (Equiv.Perm (Fin 2058))) := by
  cases i
  · exact Actor0.perm_normalizes_odd
  · exact Actor1.perm_normalizes_odd

/-- A genuine ambient-normalizer actor preserving both literal candidates. -/
def actor (i : Bool) : permutationPairStabilizer (candidateTwo i 0) (candidateOdd i 0) :=
  ⟨⟨permutation i, permutation_mem_normalizer i⟩,
    (mem_permutationPairStabilizer_iff _ _ _).mpr
      ⟨permutation_normalizes_two i, permutation_normalizes_odd i⟩⟩

theorem actor_coe (i : Bool) : (actor i).val.val = permutation i := rfl

theorem actor_conj_basis (i : Bool) (k : Fin 2) :
    (actor i).val.val * representation (basisGenerator i 0 k) * (actor i).val.val⁻¹ =
      representation (imageElement i k) := by
  cases i
  · exact Actor0.conj_basis k
  · exact Actor1.conj_basis k

/-- The actual restricted conjugation in the marked plane coordinates. -/
theorem actor_coordinates (i : Bool) :
    MulAut.congr (candidateOddEquiv i 0)
      (permutationPairAction (candidateTwo i 0) (candidateOdd i 0) (actor i)) =
        coordinateAction i := by
  apply plane_aut_ext
  intro k
  apply (candidateOddEquiv i 0).symm.injective
  change (candidateOddEquiv i 0).symm ((candidateOddEquiv i 0)
    (permutationPairAction (candidateTwo i 0) (candidateOdd i 0) (actor i)
      ((candidateOddEquiv i 0).symm (coordinateVector k)))) = _
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  apply representation_injective
  rw [permutationPairAction_apply, candidateOddEquiv_symm_vector,
    candidateOddEquiv_symm_image]
  exact actor_conj_basis i k

theorem actor_false_coordinates :
    MulAut.congr (candidateOddEquiv false 0)
      (permutationPairAction (candidateTwo false 0) (candidateOdd false 0) (actor false)) =
        rotation := actor_coordinates false

theorem actor_true_coordinates :
    MulAut.congr (candidateOddEquiv true 0)
      (permutationPairAction (candidateTwo true 0) (candidateOdd true 0) (actor true)) =
        rotation⁻¹ := actor_coordinates true

theorem actor_coordinates_not_diagonal (i : Bool) :
    MulAut.congr (candidateOddEquiv i 0)
      (permutationPairAction (candidateTwo i 0) (candidateOdd i 0) (actor i)) ∉ diagonal := by
  rw [actor_coordinates]
  exact coordinateAction_not_mem_diagonal i
end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
