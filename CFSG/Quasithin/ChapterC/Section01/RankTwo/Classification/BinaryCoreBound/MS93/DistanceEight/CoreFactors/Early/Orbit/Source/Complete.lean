module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.SmallSeed.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.SourceApplications
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Core

/-!
# The complete early orbit source and its literal higher-layer consumers

The original path now has every first-hat identity and both commutator
bounds, so the complete (4.5.2)--(4.5.3) record is constructed. No layer
identity, product containment, or module-splitting premise is retained.
The same vertices then bound the first quotient and place the actual core
in the third hat layer, proving the independent (4.5.4)(vi) clause.

Source: Meierfrankenfeld--Stellmacher (1993), pp.896--899. Earlier is the
independently owned genuine (4.4) input; higher quotient recognition and the
reverse core-center inclusion remain separate source obligations.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Complete
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The complete actual MS93 (4.5.2)--(4.5.3) record on the original path. -/
theorem sourceOrbitFacts (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a) :
    SourceOrbitFacts R p :=
  HatCommutators.sourceOrbitFacts_of_identity source common earlier p
    (HatIdentity.SmallSeed.identitiesOnPath common earlier p)

/-- The source path and every early orbit calculation are constructed,
conditional only on the genuine preceding source (4.4). -/
theorem sourcePath_facts_nonempty (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (a : Vertex R) (ha : color R a = false) :
    Nonempty (Σ' p : SourcePath R a, FirstFactsOnPath R geometry p ∧ SourceOrbitFacts R p) := by
  obtain ⟨p⟩ := sourcePath_nonempty source common earlier a ha
  exact ⟨⟨p, firstFactsOnPath source common earlier p, sourceOrbitFacts common earlier p⟩⟩

/-- The literal first quotient in the higher-layer argument has order at most eight. -/
theorem first_hat_quotient_bound (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : SourcePath R (alpha R)) :
    (Z R (alpha R)).relIndex (hatV R (alpha R) (p.walk.getVert 6)) ≤ 8 :=
  Higher.Quotients.hatV_relIndex_le_eight common earlier
    (HatIdentity.SmallSeed.identitiesOnPath common earlier p).center

/-- The actual core is contained in the literal third orbit layer,
with every preceding-layer hypothesis discharged. This is (4.5.4)(vi). -/
theorem core_le_third_hat (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a) :
    core R a ≤ hatSix R a (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10) := by
  let h := HatIdentity.SmallSeed.identitiesOnPath common earlier p
  have f := firstFactsOnPath source common earlier p
  apply Higher.OrbitGeometry.SourcePath.core_le_hatSix source common earlier
    (SourceApplications.higherPath geometry p) h.center
    (h.forward 8 (by decide) (by decide) (by decide))
  · convert (f.forward 2 (by decide) (by decide) (by decide)).hatW_product using 1 <;> simp only [SourceApplications.higherPath, Nat.reduceAdd, p.center_eq]
  · convert (f.forward 4 (by decide) (by decide) (by decide)).hatW_product using 1 <;> simp only [SourceApplications.higherPath, Nat.reduceAdd, p.center_eq]
  · exact HatCommutators.forward_second_bound_of_identity common earlier p h
      (i := 8) (by decide) (by decide) (by decide)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Complete
