module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceIrreducible
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Inputs
public import CFSG.Quasithin.Chapter4.Defs

/-!
# The two source inputs for the Mathieu generation bound

The normalized case of 4.4.14 makes the literal odd Hall subgroup of
H ∩ N_G(L) faithful on L/O₂(L). The separate Mathieu calculation bounds
the Cartan parameter of an automorphism subgroup containing all inner
automorphisms of a quasisimple cover. These are proof obligations, not
asserted source results. In particular the second input retains both central
covers and intermediate outer extensions.

The assembly in `MathieuGeneration` constructs the Hall subgroup from E.2.2,
maps its witness through actual quotient conjugation, and discharges the
comparison between the two central quotients. It remains conditional until
both inputs below are proved.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 4.4.14,
E.3.36--39 and 7.3.4, printed pp.624--625, 239--240 and 699.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter12.Section02 ChapterE ChapterE.Section06.FixedPointBounds
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u

/-- The intrinsic Mathieu calculation used by the original quotient action.
The inner-subgroup condition is essential: an arbitrary cyclic subgroup of
order seven would have Cartan parameter three. -/
def MathieuCartanRestriction : Prop :=
  ∀ (X : Type u) (_ : Group X) (_ : Finite X), IsQuasisimple X →
    HasMathieuCentralQuotient X →
    ∀ A : Subgroup (MulAut X), MulAut.innerSubgroup X ≤ A → nPrime A ≤ 2

/-- The normalized Mathieu instance of 4.4.14, on the original chosen module.
The centralizer is the action kernel on L/O₂(L), not on a family tag and
not the centralizer of L in G. -/
def SourceMathieuHallFaithfulAt {G : Type u} [Group G] [Finite G]
    (T : Sylow 2 G) : Prop :=
  ∀ (L V : Subgroup G) (D : ChosenModule T L V),
    Hypothesis1223 KnownSimple.IsKnownSimple T L →
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
    V = D.sourceOrbit →
    ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
    HasMathieuCentralQuotient D.orbitComponent →
    ¬ IsFFModule D.sourceOrbitNormalizerRepresentation →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < generationParameter H →
      ∀ B : Subgroup H, B ≤ (normalizer (L : Set G)).subgroupOf H →
        IsHallSubgroup oddPrimes (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)) →
        IsMulCommutative B →
        (B.map H.subtype : Set G) * (T : Set G) =
          (T : Set G) * (B.map H.subtype : Set G) →
        B.map H.subtype ⊓ Chapter4.sectionCentralizer L = ⊥

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
