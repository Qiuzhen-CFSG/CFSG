module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Generation.Reduction
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Generation.Field
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Generation.OtherSieve

/-!
# Assembly of the ordinary residual-transfer branch

If the prime-to-p residuals indexed by the odd prime ranks of L generate Lᵣ,
the ordinary identities in 16.4.5 transfer Lᵣ into L′. In the binary field
branch, the actual matrix action proves that the centralizers in L of the
involutions of Lᵣ generate L. Tight embedding therefore excludes Lᵣ ≤ K′.

The two assembly lemmas retain the exhaustive table sieve and component
placement as explicit premises. They do not assert source 16.4.8: proving
those premises from the earlier chapter statements remains necessary.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the ordinary
branch of the proof of Lemma 16.4.8, printed p.1188.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual

open Subgroup

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The proved field generation equality eliminates the K′ placement.
The component-placement dichotomy is a separate source obligation. -/
theorem involutionResidual_le_conjugate_of_binaryField_placement
    (h : IntersectionSetup T z L g R)
    (hnot : ¬ L ≤ normalizer ((centralizer (L : Set G)).conjBy g : Set G))
    (hr : r ∈ R) (hfield : IsBinaryFieldInvolution (involutionAction h hr))
    (hplace : involutionResidual L r ≤ L.conjBy g ∨
      involutionResidual L r ≤ (centralizer (L : Set G)).conjBy g) :
    involutionResidual L r ≤ L.conjBy g :=
  hplace.resolve_right (involutionResidual_not_le_conjugate_centralizer h hnot
    (involutionResidual_centralizers_generate_of_binaryField h hr hfield))

/-- Conditional assembly of the ordinary branch. Its table and placement
premises must be proved before this yields source 16.4.8. -/
theorem ordinary_residual_transfer_of_sieve_and_placement
    (h : IntersectionSetup T z L g R)
    (hnot : ¬ L ≤ normalizer ((centralizer (L : Set G)).conjBy g : Set G))
    (hr : r ∈ R)
    (hres : ∀ p ∈ residualPrimes (L.conjBy g),
      (primeToResidual p (involutionCentralizer r)).map
        (involutionCentralizer r).subtype = L.conjBy g)
    (hsieve : rankResidualSpan L (involutionResidual L r) = involutionResidual L r ∨
      IsBinaryFieldInvolution (involutionAction h hr))
    (hplace : IsBinaryFieldInvolution (involutionAction h hr) →
      involutionResidual L r ≤ L.conjBy g ∨
        involutionResidual L r ≤ (centralizer (L : Set G)).conjBy g) :
    involutionResidual L r ≤ L.conjBy g := by
  rcases hsieve with hspan | hfield
  · exact involutionResidual_le_conjugate_of_rankSpan_eq hspan hres
  · exact involutionResidual_le_conjugate_of_binaryField_placement h hnot hr hfield
      (hplace hfield)

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual
