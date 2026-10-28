module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Characters
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Commutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction

/-!
# The literal MS93 Z-case geometry from the preceding source layers

The character comparison gives the equal-Z containment and the unequal-Z
product intersection. The neighboring quotient-action estimate supplies the
commutator containment in both products. Together they construct the published
`ZCaseGeometry` contract and feed its actual `pair_bounds_of_Z_geometry` consumer.

`zCaseGeometry_of_marked_sections` constructs both inputs using `Pairings`
and `NeighborAction`. Thus no character comparison, neighboring action bound
or Z-case conclusion remains a premise of this construction. The sections
use the same `common.natural.marking`; the neighboring section is pulled back
along an actual conjugator. All three forward vertices are retained. The
proof uses only the path's actual turns and the supplied first-layer identities,
so it makes no identification of unrelated forward choices.

The explicit earlier inputs are (4.5.1)(v), the first-layer identities
(4.5.3)(i) at a,c,d, and the forward commutator bound (4.5.3)(ii) at c,d.
The pair-bound consumer additionally uses the literal (4.5.3)(iii) at c.
Their producer is `qt-c01-ms93-core-factors-early-layers`; the marked sections
belong to `qt-c01-ms93-higher-marked-quotients`. These allowed earlier-source
premises retain their discharge with `qt-c01-ms93-higher-conjugate-pairs`.
The opening noncentrality and the rest of (4.5.5) also remain with that parent.
No erroneous `Early.OrbitFacts` generation premise or final Q/derived bound
is used. The earlier conditional comparison APIs are preserved below.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5.5), printed p.899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {R : Subgroup M}

/-- Assemble the three literal Z-case assertions from compatible character
comparisons and the neighboring quotient-action estimate. -/
theorem zCaseGeometry_of_characterComparisons [Finite M]
    {geometry : Geometry R} (earlier : Earlier R geometry)
    {a : Vertex R} (p : Higher.SourcePath a) (pairings : CharacterComparisons p)
    (hneighbor : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10), Q R a⁆ ≤
      hatV R a (p.walk.getVert 6) ⊔ hatV R (p.walk.getVert 6) (p.walk.getVert 8)) :
    ZCaseGeometry p where
  equal_Z_span := equal_Z_span_of_characters p pairings
  unequal_Z_commutator := fun g _ => pair_commutator_products_of_neighbor_bound earlier p hneighbor g
  unequal_Z_intersection := unequal_Z_intersection_of_characters earlier p pairings

/-- Actual consumer application. The earlier (4.5.3)(iii) estimate is used by
TwoCases only after the geometric character and neighboring-action obligations
have supplied the three literal Z-case assertions. -/
theorem pair_bounds_of_characterComparisons [Finite M] {L : Subgroup M}
    {geometry : Geometry R} (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R)) (pairings : CharacterComparisons p)
    (hneighbor : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10), Q R (alpha R)⁆ ≤
      hatV R (alpha R) (p.walk.getVert 6) ⊔ hatV R (p.walk.getVert 6) (p.walk.getVert 8))
    (hW : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6)) :
    ∀ g : stabilizer R (alpha R),
      ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
        rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁆ ≤
          hatV R (alpha R) (p.walk.getVert 6) :=
  pair_bounds_of_Z_geometry source common earlier p
    (zCaseGeometry_of_characterComparisons earlier p pairings hneighbor) hW

/-- The two source Z-cases, with both the character comparisons and the
neighboring action bound discharged. Only actual marked sections and literal
(4.5.1)--(4.5.3) clauses remain explicit. The neighboring section retains
the actual c,d,e under its pullback to alpha and uses the common marking. -/
theorem zCaseGeometry_of_marked_sections [Finite M] {L : Subgroup M}
    {geometry : Geometry R} (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R))
    (firstSection : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (secondSection : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (k : FreeAmalgam R) (hk : act R k (alpha R) = p.walk.getVert 6)
    (neighborSection : MarkedPairSection source common
      (rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) k⁻¹)
      (rightConjugate (hatV R (p.walk.getVert 6) (p.walk.getVert 8)) k⁻¹) true)
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (hH : Nat.card (H R (alpha R)) = 4)
    (hforward : ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8)) : ZCaseGeometry p := by
  obtain ⟨pairings⟩ := Pairings.characterComparisons common earlier p
    firstSection secondSection hVa hVc hH hforward
  have hneighbor := NeighborAction.neighbor_bound common earlier p
    k hk neighborSection hVa hVd hH
  exact zCaseGeometry_of_characterComparisons earlier p pairings hneighbor

/-- Apply the constructed geometry to the actual pair-bound consumer.
The equal-Z branch uses (4.5.3)(iii); the unequal-Z branch uses the proved
ordered-product intersection. No Q bound or derived bound is an input. -/
theorem pair_bounds_of_marked_sections [Finite M] {L : Subgroup M}
    {geometry : Geometry R} (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R))
    (firstSection : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (secondSection : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (k : FreeAmalgam R) (hk : act R k (alpha R) = p.walk.getVert 6)
    (neighborSection : MarkedPairSection source common
      (rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) k⁻¹)
      (rightConjugate (hatV R (p.walk.getVert 6) (p.walk.getVert 8)) k⁻¹) true)
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (hH : Nat.card (H R (alpha R)) = 4)
    (hforward : ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8))
    (hW : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6)) :
    ∀ g : stabilizer R (alpha R),
      ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
        rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁆ ≤
          hatV R (alpha R) (p.walk.getVert 6) :=
  pair_bounds_of_Z_geometry source common earlier p
    (zCaseGeometry_of_marked_sections source common earlier p
      firstSection secondSection k hk neighborSection hVa hVc hVd hH hforward) hW

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry
