module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators.Path
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators.Preliminary

/-!
# MS93 (4.5.3)(ii--iii) from the first-hat identities

The marked natural-section calculation supplies the preliminary displacement
into Z_a Z_c. The printed intersection bound and the reflected product from
(4.5.1)(iv) sharpen this to Z_c. Conjugate generation gives the second-layer
bound. All translations and reflections retain the supplied path and its
actual indexed vertices.

The SourceOrbitFacts constructor below discharges both commutator premises,
relative normality, generation and the ordered first-hat product. Only the
independently produced first-hat identities remain explicit, besides the
genuine preceding source inputs. Their discharge remains with the parent
assembly of (4.5.3)(i); no preliminary displacement premise remains here.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.897--898.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Both directions of (4.5.3)(ii) at centers four, six, eight and ten.
The preliminary displacement is proved from the supplied first-hat identities. -/
theorem first_bounds_of_identity (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    (identity : HatIdentitiesOnPath R p) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi10 : i ≤ 10) :
    (⁅hatV R (p.walk.getVert i) (p.walk.getVert (i + 2)),
      Q R (p.walk.getVert (i + 2))⁆ ≤ Z R (p.walk.getVert (i + 2))) ∧
    (⁅hatV R (p.walk.getVert i) (p.walk.getVert (i - 2)),
      Q R (p.walk.getVert (i - 2))⁆ ≤ Z R (p.walk.getVert (i - 2))) :=
  first_bounds common earlier p identity (preliminaryOnPath common earlier p identity)
    hi hi4 hi10

/-- The forward instances of (4.5.3)(iii) at centers four, six and eight,
conditional only on the first-hat identities and the preceding source inputs. -/
theorem forward_second_bound_of_identity (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    (identity : HatIdentitiesOnPath R p) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi8 : i ≤ 8) :
    ⁅hatW R (p.walk.getVert i) (p.walk.getVert (i + 2)) (p.walk.getVert (i + 4)),
      Q R (p.walk.getVert i)⁆ ≤ Z R (p.walk.getVert i) :=
  forward_second_bound common earlier p identity (preliminaryOnPath common earlier p identity)
    hi hi4 hi8

/-- The reflected instances of (4.5.3)(iii) at centers six, eight and ten,
with the subtraction guards and the vertices of the original path retained. -/
theorem backward_second_bound_of_identity (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    (identity : HatIdentitiesOnPath R p) {i : ℕ}
    (hi : Even i) (hi6 : 6 ≤ i) (hi10 : i ≤ 10) :
    ⁅hatW R (p.walk.getVert i) (p.walk.getVert (i - 2)) (p.walk.getVert (i - 4)),
      Q R (p.walk.getVert i)⁆ ≤ Z R (p.walk.getVert i) :=
  backward_second_bound common earlier p identity (preliminaryOnPath common earlier p identity)
    hi hi6 hi10

/-- MS93 (4.5.3)(ii) at the original center, with (i) explicitly supplied. -/
theorem hatV_commutator_of_identity (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    (identity : HatIdentitiesOnPath R p) :
    ⁅hatV R a (p.walk.getVert 6), Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6) := by
  simpa only [p.center_eq] using (first_bounds_of_identity common earlier p identity
    (i := 4) (by decide) (by decide) (by decide)).1

/-- MS93 (4.5.3)(iii) at the original center, with (i) explicitly supplied. -/
theorem hatW_commutator_of_identity (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    (identity : HatIdentitiesOnPath R p) :
    ⁅hatW R a (p.walk.getVert 6) (p.walk.getVert 8), Q R a⁆ ≤ Z R a := by
  simpa only [p.center_eq] using forward_second_bound_of_identity common earlier p identity
    (i := 4) (by decide) (by decide) (by decide)

/-- The actual corrected source record, with only the independent (4.5.3)(i)
identity premise left to the parent assembly. Both commutator fields are proved
above; relative normality, generation and the ordered product are also discharged. -/
theorem sourceOrbitFacts_of_identity (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) (identity : HatIdentitiesOnPath R p) :
    SourceOrbitFacts R p where
  Z_le_pair := (center_normality common earlier p).1
  Z_normal_pair := (center_normality common earlier p).2
  local_generation := local_generation source common earlier p
  reflected_Z_le_pair := (reflected_normality common earlier p).1
  reflected_Z_normal_pair := (reflected_normality common earlier p).2
  hatV_eq := identity.center
  hatV_product := hatV_product_of_eq common
    (by simpa only [p.center_eq] using p.even_color (i := 4) (by decide) (by decide)) identity.center
  hatV_commutator := hatV_commutator_of_identity common earlier p identity
  hatW_commutator := hatW_commutator_of_identity common earlier p identity

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
