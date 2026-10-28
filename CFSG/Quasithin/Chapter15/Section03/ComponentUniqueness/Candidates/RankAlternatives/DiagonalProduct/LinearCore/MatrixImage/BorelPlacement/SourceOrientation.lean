module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.BorelPlacement.Source
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.BorelPlacement.ThetaCore

/-!
# The original oriented Borel planes from the marked source branch

The selected outer cubic actor puts Y₊ outside L. Full local Sylow invariance
then discharges the last premise of the theta-core assembly. In particular,
the field degree is prime to three, theta of the actual Borel has two-core
S ∩ L and quotient of order three, and theta equals O²(Y₊ ∩ L).

The cyclic-plane theorem and intrinsic Borel rigidity and root calculations
therefore give the two original planes with their interchange, in the same
projective marking. The constructor requires only the genuine earlier local
conclusions and the marked linear branch; it assumes neither a product
decomposition of Y₊ nor any Borel or matrix-calculation record.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.2--12, 15.3.25, 15.3.33, 15.3.36--37, and the Borel and plane argument
in the proof of 15.3.38, printed pp.1121--1125 and 1134--1136.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel

variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

/-- Construct the actual oriented Borel planes from the marked source branch.
All Sylow, theta-core, quotient, rigidity, and root inputs are discharged.
The original planes, their interchange, and the supplied marking are retained. -/
theorem orientedBorelData_of_marked_source
    (hI : I ∈ d.Hplus) (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hrL : primeRank 3 L = 2) (hrY : primeRank 3 d.Yplus = 2) (e : Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    {y : G} (hy : y ∈ d.Yplus) (hdiag : c.Diagonal y) :
    Nonempty (OrientedBorelData d.M d.Yplus d.S L d.V₁ d.V₂ c) :=
  orientedBorelData_of_marked_stability hI hLI hL hrL hrY e hn heven c hy hdiag
    (component_sylow_invariant_of_marked_local hI hLI hL hrL hrY e hn heven c hy hdiag)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
