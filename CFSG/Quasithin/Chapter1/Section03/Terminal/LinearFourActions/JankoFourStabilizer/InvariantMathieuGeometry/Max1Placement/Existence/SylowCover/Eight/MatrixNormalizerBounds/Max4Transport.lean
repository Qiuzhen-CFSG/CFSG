module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Definitions
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.Proper

/-!
# The precise max4-eight comparison needed for row two

The normal eight already constructed inside literal max4 is embedded with
that subgroup's inclusion. An ambient conjugacy to the third prescribed
Sylow eight transports a full ambient normalizer bound to the first
alternative of the row contract. Both the conjugacy and the normalizer
bound remain explicit independent obligations.

Source context: Kleidman–Wilson (1988), pp.484–510, and Aschbacher–Smith
A.3.12. The eight's actual word table and ATLAS provenance are retained in
`Max4.NormalEight`; no abstract shape or order comparison replaces conjugacy.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Subgroup Janko4 Janko4.LocalStructure.SymmetricLinear

/-- The already certified max4 eight, with its literal ambient embedding. -/
abbrev max4Eight : Subgroup Model := NormalEight.eight.map max4Subgroup.subtype

/-- The chosen orientation sends the certified max4 eight to the prescribed
row-two subgroup. It therefore uses the same conjugator in the row bound. -/
theorem row_two_of_max4_eight_conjugacy
    (hconj : ∃ k : Model, max4Eight.map (MulAut.conj k).toMonoidHom = U 2)
    (hN : normalizer (max4Eight : Set Model) ≤ max4Subgroup) :
    EightNormalizerAlternative (U 2) := by
  obtain ⟨k, hk⟩ := hconj
  left
  refine ⟨k, ?_⟩
  rw [← hk, ← map_equiv_normalizer_eq]
  exact map_mono hN

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
