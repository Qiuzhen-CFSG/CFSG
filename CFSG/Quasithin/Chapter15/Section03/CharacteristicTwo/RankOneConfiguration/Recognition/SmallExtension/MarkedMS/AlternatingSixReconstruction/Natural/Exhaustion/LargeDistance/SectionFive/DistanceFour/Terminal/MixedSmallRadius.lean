module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.LargeImage
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedSmallRadius

/-!
# Mixed-plane midpoint radii at distance four

Every critical image at distance four is small. In the mixed-plane branch,
a larger predecessor-radius image would contain a large critical seed on
an actual repathing of the same graph. Excluding that seed identifies the
whole midpoint radius image, commutator and full starting kernel with those
of the critical endpoint. Both moving covers and their central attachments
are retained.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the mixed-plane small-radius argument of (5.7)--(5.8), applied after
the large-image exclusion in (5.12)(2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- At distance four the whole mixed midpoint radius has exactly the
endpoint image and full critical kernel at the starting vertex. -/
theorem mixed_midpoint_radius_data_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    let W := V d.radical (p.walk.getVert 2)
    (Q d.radical a).relIndex W = 2 ∧
      Q d.radical a ⊔ W = Q d.radical a ⊔ Z d.radical z ∧
      ⁅Z d.radical a,W⁆ = ⁅Z d.radical a,Z d.radical z⁆ ∧
      Z d.radical a ⊓ centralizer (W : Set (FreeAmalgam d.radical)) =
        Z d.radical a ⊓ Q d.radical z := by
  have hp := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p
  have hr : (Q d.radical a).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2))) ≤ 2 := by
    by_contra! hlarge
    obtain ⟨c,_,q,hq,_,_⟩ :=
      MixedSmallSeeds.mixed_predecessor_radius_large_seed_knownSimple
        (by omega) u him p hp hlarge
    have hqsmall := critical_image_small_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb q
    omega
  have hout := MixedSmallRadius.small_predecessor_radius_data
    (fullSymmetricAction_knownSimple h e hz hn d (by omega))
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) (by omega) p hp hr
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  simpa only [hl] using hout

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

