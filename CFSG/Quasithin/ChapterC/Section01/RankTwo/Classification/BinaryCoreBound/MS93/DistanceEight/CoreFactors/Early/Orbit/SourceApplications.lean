module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Path
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Unequal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.Source

/-!+# Applying corrected early normality to the actual higher-layer path

The higher source path below retains exactly the supplied early walk, its
endpoints and every indexed vertex. The tree gives its shortest-path field.
The reflected normality of (4.5.2)(i) and the constructed (4.5.1)(i) record
then discharge both early premises in the replacement applications.

The replacement Witness and its genuine independent critical hypotheses
remain explicit. These results do not prove the unequal-Z contradiction,
reverse normalization, the moving-section classification or (4.5.3).
The quotient application still requires the latter's first hat identity.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.895--899.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.SourceApplications
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The exact early walk, with the higher path's geodesic proof filled in. -/
def higherPath (geometry : Geometry R) {a : Vertex R} (p : SourcePath R a) :
    Higher.SourcePath a where
  first := p.first
  last := p.last
  walk := p.walk
  start_color := p.start_color
  length_eq := p.length_eq
  shortest := p.shortest (geometry := geometry)
  center_eq := p.center_eq
  turns := p.turns
  critical := p.critical
  distinct_Z := p.edge_Z_ne

/-- Both higher branches receive the original walk without any reselection. -/
theorem higherPath_walk {a : Vertex R} (p : SourcePath R a) :
    (higherPath geometry p).walk = p.walk := rfl

private theorem first_commutator [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) :
    ⁅V R a, V R (p.walk.getVert 8)⁆ = H R a ⊓ H R (p.walk.getVert 8) := by
  simpa only [p.center_eq] using
    ((firstFactsOnPath source common earlier p).forward 4
      (by decide) (by decide) (by decide)).commutator_eq

/-- The actual selected endpoint normalizes the forward Z-layer, with the
first-calculation and reflected-normality premises fully discharged. -/
theorem endpoint_normalizes_forward_Z [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {g : stabilizer R a}
    (w : Higher.OrbitGeometry.Replacement.Witness (higherPath geometry p) g) :
    Z R w.endpoint ≤ normalizer (Z R (p.walk.getVert 8) : Set (FreeAmalgam R)) :=
  Higher.OrbitGeometry.Replacement.Unequal.endpoint_normalizes_forward_Z common earlier
    (higherPath geometry p) w (first_commutator common earlier p)
    (Source.reflected_normality common earlier p).2

/-- The same selected endpoint has displacement inside the original forward
edge layer. Both early source inputs are proved on this supplied walk. -/
theorem endpoint_forward_commutator_le_edge [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {g : stabilizer R a}
    (w : Higher.OrbitGeometry.Replacement.Witness (higherPath geometry p) g) :
    ⁅Z R w.endpoint, Z R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 7) :=
  Higher.OrbitGeometry.Replacement.Unequal.endpoint_forward_commutator_le_edge common earlier
    (higherPath geometry p) w (first_commutator common earlier p)
    (Source.reflected_normality common earlier p).2

/-- Apply the displacement bound to the genuine prescribed replacement.
The independent critical conditions are retained; no reverse normalization
or unequal-Z contradiction is asserted. -/
theorem forward_edge_Z_not_le_endpoint [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) (g : stabilizer R a)
    (hd : (cosetGraph R).dist (act R g (p.walk.getVert 8)) (p.walk.getVert 8) = 8)
    (hn : ¬ Z R (act R g (p.walk.getVert 8)) ≤ Q R (p.walk.getVert 8))
    (w : Higher.OrbitGeometry.Replacement.Witness (higherPath geometry p) g) :
    ¬ Z R (p.walk.getVert 7) ≤ Z R w.endpoint :=
  Higher.OrbitGeometry.Replacement.Unequal.forward_edge_Z_not_le_endpoint common earlier
    (higherPath geometry p) g hd hn w (first_commutator common earlier p)
    (Source.reflected_normality common earlier p).2

/-- The proved first-hat identity, once supplied by its source calculation,
feeds the existing literal relative-index consumer. This conditional adapter
does not construct that identity or a moving-section model. -/
theorem hatV_relIndex_le_eight
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : SourcePath R (alpha R)) (identity : Source.HatIdentitiesOnPath R p) :
    (Z R (alpha R)).relIndex (hatV R (alpha R) (p.walk.getVert 6)) ≤ 8 :=
  Higher.Quotients.hatV_relIndex_le_eight common earlier identity.center

/-- Application to the existing marked dual-section construction on the
same path. The independent genuine moving-section model and the remaining
(4.5.3)(i) identity are both retained explicitly. -/
theorem dual_section_of_moving_section [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : SourcePath R (alpha R)) (identity : Source.HatIdentitiesOnPath R p)
    (n : Higher.MarkedPairSection source common
      (⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
          Ltilde R (alpha R)⁆ ⊔ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) false) :
    Nonempty (Higher.MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R))) :=
  Higher.Quotients.dual_section_of_moving_section common earlier
    (higherPath geometry p) identity.center n

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.SourceApplications
