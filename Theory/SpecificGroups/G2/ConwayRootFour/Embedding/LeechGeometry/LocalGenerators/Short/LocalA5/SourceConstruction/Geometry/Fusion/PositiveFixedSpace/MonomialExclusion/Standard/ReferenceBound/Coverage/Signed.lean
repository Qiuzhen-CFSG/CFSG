module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Coverage.Signed.Verification

/-!
# Exhaustive signed coverage of the reference centralizer normal form

Decode every hex and parity parameter using finite equivalences. The two square
equations imply the parity-independent translation checks, whose exhaustive
verification selects a row. Its checked coordinate formulas turn the remaining
sign equation into the packed parity check. The resulting original candidate
index reconstructs both the sign and the pullback in the literal flat indexing.

This proves `SignedCoverage` independently of `ColumnCoverage`. It discharges the
signed finite obligation of the reference-centralizer assembly, not the separate
column enumeration or fixed-space calculation. Source context: Aschbacher,
*Sporadic Groups* (1994), Lemma 49.5, pp.283–284, with the convention on p.269.
-/

open Atlas.Codes
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage

namespace Signed

private theorem matches_of_packed (q : Fin 16) (a : Fin 4) (r : Fin 32)
    (hc : Coordinates q a) (hk : PackedCheck q a)
    (hs : ∀ i, signedWord (columnCandidate q)
      (decodeHex ((translationData.get q).get a).1) (decodeParity r) i +
      signedWord (columnCandidate q)
        (decodeHex ((translationData.get q).get a).1) (decodeParity r)
        (markedPull (columnCandidate q)
          (hexEncoder (decodeHex ((translationData.get q).get a).1)) i) = 0) :
    ∃ k : Fin 512, ParameterMatches (columnCandidate q)
      (decodeHex ((translationData.get q).get a).1) (decodeParity r) k := by
  let row := (translationData.get q).get a
  have hsign (i : Fin 24) :
      signedWord (columnCandidate q) (decodeHex row.1) (decodeParity r)
        (StandardCoordinates.flat.symm i) =
      maskBit (row.2.1 ^^^ parityMasks.get r) i := by
    exact (congrArg₂ (· + ·) (hc.1 i) (parity_correct r i)).trans
      (maskBit_xor _ _ _).symm
  have hpull (i : Fin 24) :
      markedPull (columnCandidate q) (hexEncoder (decodeHex row.1))
        (StandardCoordinates.flat.symm i) =
      StandardCoordinates.flat.symm (pullData.get row.2.2 i) := by
    apply StandardCoordinates.flat.injective
    simpa only [Equiv.apply_symm_apply] using hc.2 i
  have hz (i : Fin 24) : maskBit (row.2.1 ^^^ parityMasks.get r) i +
      maskBit (row.2.1 ^^^ parityMasks.get r) (pullData.get row.2.2 i) = 0 := by
    have hi := hs (StandardCoordinates.flat.symm i)
    rw [hpull i, hsign i, hsign (pullData.get row.2.2 i)] at hi
    exact hi
  have hd := hk r hz
  refine ⟨((witnessData.get q).get a).get r, ?_, ?_⟩
  · intro i
    rw [hsign]
    change _ = maskBit (candidateData _).1 i
    rw [hd]
  · intro i
    rw [hc.2 i]
    change _ = pullData.get (candidateData _).2 i
    rw [hd]

private theorem coverage_of_checks (ha : ∀ q, Admitted q)
    (hc : ∀ q a, Coordinates q a) (hk : ∀ q a, PackedCheck q a) :
    SignedCoverage := by
  intro q u r hp hs
  obtain ⟨h,rfl⟩ := decodeHex_surjective u
  obtain ⟨s,rfl⟩ := decodeParity_surjective r
  obtain ⟨a,rfl⟩ := ha q h (translationChecks_of_square _ _ _ hp hs)
  exact matches_of_packed q a s (hc q a) (hk q a) hs

end Signed

/-- Every normalized signed square-one parameter occurs in the original candidate table. -/
theorem signedCoverage : SignedCoverage :=
  Signed.coverage_of_checks
    (fun q => (Signed.verified q).1)
    (fun q a => ((Signed.verified q).2 a).1)
    (fun q a => ((Signed.verified q).2 a).2)

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage
