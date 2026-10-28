module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.BorelPlacement.SylowInvariance

/-!
# Source placement of the actual linear Sylow normalizer

Solvability of the actual local group Y₊S forces its projective action to
preserve the specified component Sylow. The full preimage is S ∩ L, so the
characteristic-two Borel calculation and 15.3.33(1) place its normalizer
preimage in M. This discharges the invariance premise of the placement
reduction, retaining the supplied field and quotient equivalence.

Both the even-degree PSL₃ branch and the central two-cover over the field
of order four are included. No ambient product decomposition is required.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.11--12, 15.3.33 and 15.3.36--38, printed pp.1123--1125 and 1134--1136.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage

variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

/-- The actual quotient Sylow, its Borel placement, and invariance under every
element of Y₊, for the supplied even-degree projective coordinates. -/
theorem SourceSetup.borelPlacement_of_even_card (h : SourceSetup d I L)
    (hn : d.Yplus ≤ normalizer (L : Set G))
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hnpos : 0 < n) (heven : Even n) (hcard : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,F)) :
    Nonempty (BorelPlacement d.Yplus d.S d.M L hn e) :=
  h.borelPlacement_of_sylow_invariant hn e ⟨n, hnpos, hcard⟩
    (le_sup_left.trans
      (h.component_sylow_invariant_of_even_card hn hnpos heven hcard e))

/-- Source placement in the selected cubic actor's original coordinates,
including the central two-cover branch over the field of order four. -/
theorem SourceSetup.borelPlacement (h : SourceSetup d I L)
    (hn : d.Yplus ≤ normalizer (L : Set G))
    (y : d.Yplus) (_hy : orderOf y = 3)
    {F : Type*} [Field F] [Finite F] (hcase : LinearCase L (Nat.card F))
    (w : DiagonalCoordinates L (y : G) F) :
    Nonempty (BorelPlacement d.Yplus d.S d.M L hn w.e) := by
  obtain ⟨n, hnpos, heven, hcard⟩ := hcase.even_card
  exact h.borelPlacement_of_even_card hn hnpos heven hcard w.e

end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage
