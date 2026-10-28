module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Gluing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.SourceRecognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.OrbitSource

/-!
# The doubled dual quotient from the two source orbit sections

The actual delta selection generates the second hat layer by two orbit
factors. The first lies in Q_d and the whole layer does not, using only
(4.5.4)(ii), (4.5.1)(iv), and the preceding edge index. Irreducibility of
the marked single factors then proves their intersection is exactly hat V.
Quotient descent constructs the two coordinates on the whole second layer.

The original constructor retains delta and the two single marked sections
as explicit inputs. `OrbitSource` supplies the complete source construction:
both orbit containments, delta selection, faithful dual recognition and gluing
follow from CommonFacts and genuine Earlier. Its simultaneous consumer keeps
both marked sections, the early orbit facts and the independent core bounds
on the same original path.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iii), pp.898--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer
open NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}
  {common : CommonFacts R source geometry}

/-- Conditional construction on the literal source path. Generation,
independence, the product map and its exact kernel are proved here; delta
selection and the two single marked sections are the remaining inputs. -/
theorem markedPair_of_orbit_sections (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (first : MarkedDualSection source common (orbitFactor p (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)))
    (second : MarkedDualSection source common (orbitFactor p δ.vertex)
      (hatV R (alpha R) (p.walk.getVert 6)))
    (horbit : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8))
    (hprod : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R))) :
    Nonempty (MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true) :=
  pair_of_generating_sections first second δ.factors_generate
    (δ.second_factor_not_le_first earlier horbit hprod)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer
