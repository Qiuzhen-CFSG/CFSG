module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Planes
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.LocalActions.Reductions

/-!
# The actual inner coordinate images of the four Held pairs

Transfer N(P)=P through the certified conjugacy for each candidate S. Every
inner actor preserving S therefore lies in S, including actors that might
move the selected local overgroup. The orbit-color certificates force its
restriction to be diagonal in the published coordinates. Conversely, two
explicit S-words preserve the pair and independently negate the marked axes.
Thus the entire inner image is exactly the diagonal four-group.

This is the conditional model calculation requested by the representative-image
assembly. That owner must discharge N(P)=P. No realization, outer-order,
simplicity, pair catalogue, or assumed action bound enters this implication.
Sources: GLS3 Table 5.3p; Aschbacher–Smith, printed pp.509–511, with the
source-fidelity qualification in docs/quasithin-proof-basis.md.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs.LocalActions.RepresentativeImages

open Held.LocalPairs.PairCoverage.LocalActions
open Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages
open Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages

private theorem coordinate_actor_vector (i : Bool) (j k : Fin 2)
    (a : actingPairStabilizer (MulAut.conj : Held.He →* MulAut Held.He)
      (candidateTwo i j) (candidateOdd i j)) :
    markedEmbedding i j (MulAut.congr (candidateOddEquiv i j)
      (innerPairAction (candidateTwo i j) (candidateOdd i j) a) (coordinateVector k)) =
      a.val * basisGenerator i j k * a.val⁻¹ := by
  rw [markedEmbedding_eq]
  change (((candidateOddEquiv i j).symm ((candidateOddEquiv i j)
    ((innerPairAction (candidateTwo i j) (candidateOdd i j) a)
      ((candidateOddEquiv i j).symm (coordinateVector k))))) : Held.He) = _
  rw [MulEquiv.symm_apply_apply]
  change a.val * (((candidateOddEquiv i j).symm (coordinateVector k)) : Held.He) * a.val⁻¹ = _
  rw [candidateOddEquiv_symm_vector]

private theorem inner_actor_mem
    (hP : normalizer (Held.LocalPairs.SylowGeometry.Calculations.representative : Set Held.He) =
      Held.LocalPairs.SylowGeometry.Calculations.representative)
    (i : Bool) (j : Fin 2)
    (a : actingPairStabilizer (MulAut.conj : Held.He →* MulAut Held.He)
      (candidateTwo i j) (candidateOdd i j)) : a.val ∈ candidateTwo i j := by
  have hn : a.val ∈ normalizer (candidateTwo i j : Set Held.He) := by
    apply mem_normalizer_iff.mpr
    intro x
    exact ((mem_automorphismPairStabilizer_iff _ _ _).mp a.property).1 x |>.symm
  rwa [candidateTwo_normalizer hP i j] at hn

private def signActor (i : Bool) (j k : Fin 2) :
    actingPairStabilizer (MulAut.conj : Held.He →* MulAut Held.He)
      (candidateTwo i j) (candidateOdd i j) :=
  ⟨actor i j k, (mem_automorphismPairStabilizer_iff _ _ _).mpr
    ⟨fun x => (mem_normalizer_iff.mp (le_normalizer (actor_mem i j k)) x).symm,
      fun x => (mem_normalizer_iff.mp (actor_normalizes_odd i j k) x).symm⟩⟩

private theorem signActor_coordinates (i : Bool) (j k : Fin 2) :
    MulAut.congr (candidateOddEquiv i j)
      (innerPairAction (candidateTwo i j) (candidateOdd i j) (signActor i j k)) =
        signChange k := by
  have hv (l : Fin 2) : MulAut.congr (candidateOddEquiv i j)
      (innerPairAction (candidateTwo i j) (candidateOdd i j) (signActor i j k))
        (coordinateVector l) = signChange k (coordinateVector l) := by
    apply (candidateOddEquiv i j).symm.injective
    apply Subtype.ext
    rw [← markedEmbedding_eq, coordinate_actor_vector, signChange_vector]
    change actor i j k * basisGenerator i j l * (actor i j k)⁻¹ = _
    rw [actor_action]
    split
    · simp only [map_inv, Subgroup.coe_inv, candidateOddEquiv_symm_vector]
    · exact (candidateOddEquiv_symm_vector i j l).symm
  exact planeAut_ext (hv 0) (hv 1)

/-- The full inner image in the already published coordinates. Its only
additional premise is the fixed representative's ambient normalizer equality. -/
theorem innerPairAction_range_map_eq_diagonal
    (hP : normalizer (Held.LocalPairs.SylowGeometry.Calculations.representative : Set Held.He) =
      Held.LocalPairs.SylowGeometry.Calculations.representative)
    (i : Bool) (j : Fin 2) :
    ((innerPairAction (candidateTwo i j) (candidateOdd i j)).range).map
      (MulAut.congr (candidateOddEquiv i j)).toMonoidHom = diagonal := by
  apply le_antisymm
  · rintro b ⟨c, ⟨a, rfl⟩, rfl⟩
    apply mem_diagonal_of_vectors
    intro k
    exact coordinates_of_conjugation i j k a.val (inner_actor_mem hP i j a) _
      (coordinate_actor_vector i j k a)
  · apply diagonal_le_of_signChanges
    intro k
    exact ⟨_, ⟨signActor i j k, rfl⟩, signActor_coordinates i j k⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs.LocalActions.RepresentativeImages
