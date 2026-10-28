module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Coverage.Contracts
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Coverage.Columns
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Coverage.Signed

/-!
# Assembly of exhaustive reference-centralizer coverage

The normal form uses the actual Golay sign, the inverse coordinate permutation,
and both marked commutation equations. Exhaustive column and signed-parameter
proofs discharge the two finite contracts, recovering the original public
`CandidateCoverage` contract and applying it to the original reference pair.
The independent fixed-vector certificates remain with the kernel-bound assembly.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5,
pp.283–284, with the convention on p.269.
-/

open Atlas.Codes Atlas.Lattices
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound

/-- Assembly discharges every normal-form premise from `CentralizerParameters`. -/
theorem candidateCoverage_of_checks (hc : Coverage.ColumnCoverage)
    (hs : Coverage.SignedCoverage) : CandidateCoverage := by
  intro m h
  obtain ⟨pi,u,r,hpi,hp,hr⟩ := Coverage.centralizer_finite_parameters m h
  obtain ⟨q,hq⟩ := hc pi hpi
  have hp' : ∀ i, monomialPull m i =
      Coverage.markedPull (Coverage.columnCandidate q) (hexEncoder u) i := by
    simpa only [hq] using hp
  have hr' : m.left.toAdd.val = Coverage.signedWord (Coverage.columnCandidate q) u r := by
    simpa only [hq] using hr
  have hi : Function.Involutive
      (Coverage.markedPull (Coverage.columnCandidate q) (hexEncoder u)) := by
    intro i
    simpa only [hp'] using h.involutive i
  have hz : ∀ i, Coverage.signedWord (Coverage.columnCandidate q) u r i +
      Coverage.signedWord (Coverage.columnCandidate q) u r
        (Coverage.markedPull (Coverage.columnCandidate q) (hexEncoder u) i) = 0 := by
    intro i
    simpa only [hp', hr'] using h.square_sign i
  obtain ⟨k,hk⟩ := hs q u r hi hz
  refine ⟨k, ?_, ?_⟩
  · intro i
    rw [hr']
    exact hk.1 i
  · intro i
    rw [hp']
    exact hk.2 i

/-- Application to the literal source reference, square, and commutation hypotheses. -/
theorem candidateMatches_of_reference_of_checks
    (hc : Coverage.ColumnCoverage) (hs : Coverage.SignedCoverage)
    (a b m : GolayMonomialGroup) (hp : ReferenceQuaternionPair a b)
    (hm : monomialEmbedding m ^ 2 = 1)
    (hma : Commute (monomialEmbedding m) (monomialEmbedding a))
    (hmb : Commute (monomialEmbedding m) (monomialEmbedding b)) :
    ∃ k : Fin 512, CandidateMatches m k :=
  candidateCoverage_of_checks hc hs m
    (centralizerParameters_of_reference a b m hp hm hma hmb)

/-- Every actual square-one reference centralizer occurs in the unchanged table,
with both its Golay sign and its inverse coordinate permutation reconstructed. -/
theorem candidateCoverage : CandidateCoverage :=
  candidateCoverage_of_checks Coverage.columnCoverage Coverage.signedCoverage

/-- The original reference, square-one, and commutation hypotheses imply
membership in the candidate table, without any further finite-check premise. -/
theorem candidateMatches_of_reference
    (a b m : GolayMonomialGroup) (hp : ReferenceQuaternionPair a b)
    (hm : monomialEmbedding m ^ 2 = 1)
    (hma : Commute (monomialEmbedding m) (monomialEmbedding a))
    (hmb : Commute (monomialEmbedding m) (monomialEmbedding b)) :
    ∃ k : Fin 512, CandidateMatches m k :=
  candidateCoverage m
    (centralizerParameters_of_reference a b m hp hm hma hmb)

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound
