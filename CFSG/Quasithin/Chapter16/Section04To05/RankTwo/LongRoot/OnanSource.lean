module

public import CFSG.Quasithin.GoldschmidtONan
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.Onan

/-!
# The Even Type source application of Goldschmidt–O’Nan

The completed source theorem supplies all four alternatives for the actual
normalizer action. The existing cover-bound argument then rules them out.
Every root-construction, action-marking and cover hypothesis is retained;
only the previously explicit Alternatives input is now discharged.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 16.5.13,
printed pp.1201–1202; GLS, Number 2, Chapter C, Proposition 14.2.
-/

@[expose] public section
open Subgroup
open Representation Representation.BinaryOffender Representation.GoldschmidtONan
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
variable {G : Type*} [Group G]

theorem no_onan_action_of_source_input [Finite G]
    {T : Sylow 2 G} {L X Z : Subgroup G} [IsElementaryAbelian 2 (space T X)]
    (S : Subgroup (action (space T X) X).range)
    (hinput : Input (representation (space T X) X) S)
    (hfixed : fixedSpace (representation (space T X) X) S =
      linearSpace (space T X) (commutingSylow T L))
    (hmoved : Representation.RegularCyclicNormalClosure.displacementSpan
      (representation (space T X) X) S ⊤ = linearSpace (space T X) Z)
    (hXL : X ≤ L) (hZ : Z ≠ ⊥) (hZV : Z ≤ space T X) (hZX : Z ≤ X)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hbound : ((T : Subgroup G) ⊓ normalizer (X : Set G)).relIndex T ≤ 2)
    (g : G) (hg : g ∈ actingGroup (space T X) X)
    (hmove : g ∉ normalizer (commutingSylow T L : Set G))
    (hcoverT : commutingSylow T L ≤ X → (T : Subgroup G) ≤ normalizer (X : Set G))
    (hcover : space T X ≤ X → CoveredImageBounds (space T X) X) : False :=
  no_onan_action_of_cover_bounds S hinput
    (CFSG.Quasithin.GoldschmidtONan.alternatives hinput) hfixed hmoved
    hXL hZ hZV hZX hTL hbound g hg hmove hcoverT hcover

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
