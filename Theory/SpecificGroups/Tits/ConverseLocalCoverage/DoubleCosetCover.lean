module

public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.AmbientCover
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Checked
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Soundness

/-!
# The eighteen Sylow double cosets of the Tits group

The established ambient cover reduces an arbitrary Atlas element to one of
8775 explicit representatives, up to a left Sylow factor. The finite kernel
certificate factors every stored representative word, with each of the five
rotation exponents, as two Sylow normal forms around a published double-coset
word. The three-point base certificate turns these pointwise computations into
equalities in the actual Atlas group. Combining the left factors gives the
unconditional cover by the eighteen marked Sylow double cosets.

Source: Parrott (1972), section 5, p.683, and the eighteen words in
`Representatives`; see `DoubleCosetCover/source/generate.py` for the reproducible
candidate calculation. All certificates are checked by Lean's kernel.
-/

namespace Tits.ConverseLocalCoverage
open ExceptionalParabolics DoubleCosetCertificate
open OuterOddSubgroups.OverlapCentralizers

private theorem ambientRep_factor (i : Fin 1755) (j : Fin 5) :
    ∃ (a b : S) (k : Fin 18), ambientRep i j = a.val * doubleCosetRep k * b.val := by
  obtain ⟨c, hc⟩ := representative_test (R1Certificate.index i) j
  refine ⟨⟨atlas1600SylowTwoNormalForm (witnessLeft c),
    atlas1600SylowTwoNormalForm_mem _⟩,
    ⟨atlas1600SylowTwoNormalForm (witnessRight c), atlas1600SylowTwoNormalForm_mem _⟩,
    witnessRep c, ?_⟩
  exact test_sound _ j c hc

/-- Every Atlas Tits element lies in one of the eighteen marked Sylow double cosets. -/
public theorem doubleCoset_cover (x : Atlas1600Group) :
    ∃ (a b : ExceptionalParabolics.S) (i : Fin 18),
      x = a.val * doubleCosetRep i * b.val :=
  doubleCoset_cover_of_ambient ambientRep_factor x

end Tits.ConverseLocalCoverage
