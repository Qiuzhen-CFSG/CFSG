module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.Contradiction

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Paths

/-!
# The A₆ radius contradiction on the original replacement

The actual moving central quotient is irreducible and natural. Its
central-cover commutator pairing bounds the moving derived subgroup by two.
The relative three-subgroups lemma identifies it with the full radius
derived subgroup. At a critical pair, a nontrivial even involution on the
original natural cover requires at least four commutators inside that same
radius derived subgroup. This contradiction excludes the A₆ image.

All critical estimates, natural coordinates, and the original all-distance
central layer are supplied by their proved producers. The full-symmetric
Section 5 exclusions remain with the same final large-distance owner.

Source: MS93 (3.8), printed pp.878--879.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (m : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h m hz)
  (r : Replacement L R)

/-- The actual critical midpoint has a nonabelian moving group of class
two with elementary central quotient and fixed full derived radius. -/
theorem exists_nonabelian_moving_radius
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) :
    ∃ c : Vertex r.radical, color r.radical c = false ∧
      ¬ IsMulCommutative (Vcirc r.radical c) ∧
      ⁅V r.radical c,V r.radical c⁆ ≤ fixedCore r.radical c ∧
      ⁅⁅Vcirc r.radical c,Vcirc r.radical c⁆,Vcirc r.radical c⁆ = ⊥ ∧
      IsElementaryAbelian 2 ((Vcirc r.radical c) ⧸ center (Vcirc r.radical c)) := by
  obtain ⟨b,hcrit⟩ := criticalPair_exists r.radical (alpha r.radical)
    ((replacementGeometry h r).exists_critical (alpha r.radical) rfl)
  let p := CriticalPath.ofPair (geometry := replacementGeometry h r) rfl hcrit
  have hlength : p.walk.length = 4 := p.length_eq_b.trans fg.distance
  let c := p.walk.getVert 2
  have hle : 2 ≤ p.walk.length := by omega
  have hc : color r.radical c = false := (p.vertex_color hle).mpr (by decide)
  have hac : (cosetGraph r.radical).dist (alpha r.radical) c = 2 := p.dist_start hle
  have hcb : (cosetGraph r.radical).dist c b = 2 := by
    rw [p.dist_end,hlength]
  exact ⟨c,hc,
    critical_midpoint_moving_not_commutative h m hz hn r himage fg
      (alpha r.radical) rfl b hcrit c hc hac hcb,
    radius_derived_le_fixed h m hz hn r himage fg c hc,
    moving_class_two h m hz hn r himage fg c hc,
    moving_quotient_elementary h m hz hn r himage fg c hc⟩

/-- Application to the original replacement: critical estimates discharge
the entire distance-four geometric premise. -/
theorem exists_nonabelian_moving_radius_of_alternating
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (hb : 2 < replacementDistance h r) :
    ∃ c : Vertex r.radical, color r.radical c = false ∧
      ¬ IsMulCommutative (Vcirc r.radical c) ∧
      ⁅V r.radical c,V r.radical c⁆ ≤ fixedCore r.radical c ∧
      ⁅⁅Vcirc r.radical c,Vcirc r.radical c⁆,Vcirc r.radical c⁆ = ⊥ ∧
      IsElementaryAbelian 2 ((Vcirc r.radical c) ⧸ center (Vcirc r.radical c)) :=
  exists_nonabelian_moving_radius h m hz hn r himage
    (Estimates.fourGeometry_of_alternating h m hz hn r himage hb)

/-- The literal endpoint action bound, with FourGeometry and both
radius displacement premises supplied by their proved producers. -/
theorem critical_moving_fixedCodim_le_two_of_alternating
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (hb : 2 < replacementDistance h r)
    (a : Vertex r.radical) (ha : color r.radical a = false) (a' : Vertex r.radical)
    (hc : CriticalPair r.radical a a' ((replacementGeometry h r).exists_critical a ha))
    (c : Vertex r.radical) (hcColor : color r.radical c = false)
    (hac : (cosetGraph r.radical).dist a c = 2)
    (hca' : (cosetGraph r.radical).dist c a' = 2) :
    letI := moving_quotient_elementary h m hz hn r himage
      (Estimates.fourGeometry_of_alternating h m hz hn r himage hb) a ha
    fixedCodim (Offenders.linearize (movingQuotientAction a))
      ((X r.radical a').subgroupOf (stabilizer r.radical a)) ≤ 2 :=
  critical_moving_fixedCodim_le_two h m hz hn r himage
    (Estimates.fourGeometry_of_alternating h m hz hn r himage hb)
    a ha a' hc c hcColor hac hca'

/-- The complete source-(3.8) radius contradiction, with no local callback. -/
theorem radiusContradiction_knownSimple :
    RadiusContradictionInput.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ L R h m hz hn r himage fg
  exact alternating_impossible h m hz hn r himage fg

/-- Direct application to the original replacement after the critical
estimates supply all distance-four geometry. -/
theorem projection_ne_alternating_knownSimple
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (m : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h m hz)
    (r : Replacement L R) (hb : 2 < replacementDistance h r) :
    (projection h m hz hn r).range ≠ alternatingGroup (Fin 6) := by
  intro himage
  exact alternating_impossible h m hz hn r himage
    (Estimates.fourGeometry_of_alternating h m hz hn r himage hb)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
