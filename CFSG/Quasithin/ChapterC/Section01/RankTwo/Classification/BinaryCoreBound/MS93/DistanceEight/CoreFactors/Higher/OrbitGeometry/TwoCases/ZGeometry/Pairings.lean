module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings.SecondDisplacement

/-!
# The marked edge-character construction for MS93

The two actual character-valued maps, their exact kernels and conjugation
compatibility are constructed in Coordinates. Edges identifies the first
neighboring image. SecondDisplacement proves the remaining second-layer
displacement using the local turn and Q_beta = Q_a join Q_c. Together these
give CharacterComparisons and both literal ordered-product applications.

The explicit source inputs are the two marked dual sections with the same
common.natural.marking, (4.5.1)(v) at a, (4.5.3)(i) at a and c, and
(4.5.3)(ii) at c,d. The marked sections are produced by
`qt-c01-ms93-higher-marked-quotients`; the preceding clauses are produced by
`qt-c01-ms93-core-factors-early-layers`. Their source-theorem discharge
remains with `qt-c01-ms93-higher-z-case-geometry`. No edge displacement,
character comparison or Z-case conclusion remains an input here.

Every conjugate uses its actual transported path vertices. No identification
of unrelated forward choices or change of marking is required.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1)--(4.5.5),
printed pp.896--899, with relative normalizers as defined on p.881.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The two compatible character comparisons from the marked sections and
literal preceding source clauses. The second edge bound is proved internally. -/
theorem characterComparisons (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (t : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hH : Nat.card (H R (alpha R)) = 4)
    (hforward : ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8)) :
    Nonempty (CharacterComparisons p) :=
  SecondDisplacement.characterComparisons common earlier p s t hVa hVc hH hforward

/-- Apply the constructed comparisons to the equal-edge step in (4.5.5). -/
theorem equal_Z_span (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (t : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hH : Nat.card (H R (alpha R)) = 4)
    (hforward : ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8))
    (g : stabilizer R (alpha R))
    (heq : Z R (p.walk.getVert 5) = Z R (act R g (p.walk.getVert 5))) :
    (Z R (p.walk.getVert 6) : Set (FreeAmalgam R)) ⊆
      (Z R (alpha R) : Set (FreeAmalgam R)) *
        (Z R (act R g (p.walk.getVert 6)) : Set (FreeAmalgam R)) := by
  obtain ⟨pairings⟩ := characterComparisons common earlier p s t hVa hVc hH hforward
  exact equal_Z_span_of_characters p pairings g heq

/-- Apply the constructed comparisons to the distinct-edge step in (4.5.5),
retaining the source order of both subgroup products. -/
theorem unequal_Z_intersection (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (t : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hH : Nat.card (H R (alpha R)) = 4)
    (hforward : ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8))
    (g : stabilizer R (alpha R))
    (hne : Z R (p.walk.getVert 5) ≠ Z R (act R g (p.walk.getVert 5))) :
    ((hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) *
      (hatV R (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R))) ∩
    ((hatV R (act R g (p.walk.getVert 6)) (act R g (p.walk.getVert 8)) : Set (FreeAmalgam R)) *
      (hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R))) =
    (hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) := by
  obtain ⟨pairings⟩ := characterComparisons common earlier p s t hVa hVc hH hforward
  exact unequal_Z_intersection_of_characters earlier p pairings g hne

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings
