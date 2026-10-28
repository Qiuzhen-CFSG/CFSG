module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Statements
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Transport

/-!
# Corrected early relative-normalizer source calculations

This leaf proves the complete (4.5.2) family from LocalSource, CommonFacts
and Earlier. It includes the precise relative containment and normality,
the correctly typed subgroup join followed by the C factor, and the
reflected input on the same path. All shifted instances are available from
Normalizer and Generation. The wrapper constructs the original source path
and its first calculations using the published Early.First producer.

The full SourceOrbitFacts contract also contains (4.5.3). Its hat-layer
identities and commutator bounds still require the D₀/D argument on
pp.897--898; this module does not claim their construction. Applications
to higher leaves are kept in the separate SourceApplications module.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.895--898.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- All corrected (4.5.2) outputs, including reflected normality, on this path.
The first-calculation input to generation is constructed internally. -/
theorem normalizerFacts (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) : SourceNormalizerFacts R p where
  Z_le_pair := (center_normality common earlier p).1
  Z_normal_pair := (center_normality common earlier p).2
  local_generation := local_generation source common earlier p
  reflected_Z_le_pair := (reflected_normality common earlier p).1
  reflected_Z_normal_pair := (reflected_normality common earlier p).2

/-- At every M-vertex, retain the same constructed path for the first
calculations and the corrected relative-normalizer calculations. -/
theorem sourcePath_normalizerFacts_nonempty (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (a : Vertex R) (ha : color R a = false) :
    Nonempty (Σ' p : SourcePath R a,
      FirstFactsOnPath R geometry p ∧ SourceNormalizerFacts R p) := by
  obtain ⟨⟨p, first⟩⟩ := sourcePath_firstFacts_nonempty source common earlier a ha
  exact ⟨⟨p, first, normalizerFacts source common earlier p⟩⟩

/-- Final assembly with the still independent (4.5.3) calculations explicit.
This proves the adapter, not the existence of those remaining source inputs.
Their unconditional discharge remains with this source assembly. -/
theorem orbitFacts_of_hat_calculations (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) (identity : HatIdentitiesOnPath R p)
    (hV : ⁅hatV R a (p.walk.getVert 6), Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6))
    (hW : ⁅hatW R a (p.walk.getVert 6) (p.walk.getVert 8), Q R a⁆ ≤ Z R a) :
    SourceOrbitFacts R p where
  toSourceNormalizerFacts := normalizerFacts source common earlier p
  hatV_eq := identity.center
  hatV_product := hatV_product_of_eq common
    (by simpa only [p.center_eq] using p.even_color (i := 4) (by decide) (by decide))
    identity.center
  hatV_commutator := hV
  hatW_commutator := hW

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source
