module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour.CriticalTriple
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour.LongRootAuxiliary

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour.MidpointMovement

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour.KernelCentrality

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour.NonfixedSeed

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour.NonfixedEdge

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour.Source

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.Source

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Geometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.EndpointModel.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Comparison.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.FrattiniCore
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.MovingSection
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# Whole G₂ core reconstruction from the MS93 commutator containment

The source Frattini containment makes the entire [O₂(L),L] equal to the
moving part of the central omega layer. The proved initial-module theorem
then supplies its actual natural moved/fixed quotient. All elementary,
central, and equivariant clauses transport from the relative component in
LR back to L, and feed the original five-way rank-two consumer.

The final critical-triple argument proves distance-four exclusion. Together
with the established distance-two theory this discharges the Frattini premise
and gives the uniform reconstruction for every original small MS-pair. The
conditional adapters remain available alongside the unconditional exports.
Source: AS C.1.31--32, pp.135--136; MS93 (3.6), p.870, (3.8), p.879,
and Main Theorem (10).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC
namespace G2Reconstruction
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

local notation "H" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)

variable (h : SmallMSPair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2)))

include h e

/-- The canonical six-space describes the whole intrinsic block quotient once
the earlier-source Frattini containment has been supplied. -/
theorem reconstruction_of_frattini_small (hsmall : FrattiniSmall L R) : G2Reconstruction L := by
  let := relative_normal h
  let := (quotientComponent_structure h e).1
  obtain ⟨hcore,helem,hcentral⟩ :=
    MSCentralOrbit.intrinsic_core_of_frattini_small K (relative_twoPerfect h) hsmall
  obtain ⟨E⟩ := (initial_moved_natural h e).2
  have hm := BlockMovingSection.model_of_moving
    (omegaCenterIn (pCore 2 H)) K
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (central_omega_centralizer h e).symm)
    hcore (cComponentTwoCoreQuotientEquiv h.component) (fun _ => rfl)
    (Representation.g2DerivedNatural (ZMod 2)) E
  let eL : K ≃* L := subgroupOfEquivOfLe le_sup_left
  have hU : (blockU K).map eL.toMonoidHom = blockU L := by
    rw [blockU,map_commutator,pCore_map_iso,map_top_of_surjective _ eL.surjective,blockU]
  refine ⟨?_,?_,?_⟩
  · let := helem
    rw [← hU]
    exact IsElementaryAbelian.map eL.toMonoidHom
  · rw [← hU,← pCore_map_iso 2 eL]
    rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨y,hy,rfl⟩
    exact (map_mul eL y x).symm.trans
      ((congrArg eL (mem_centralizer_iff.mp (hcentral hx) y hy)).trans (map_mul eL x y))
  · obtain ⟨r,⟨model⟩,hr⟩ := hm.of_mulEquiv eL
    have he : r = g2TwoNaturalAction := by
      ext g v
      exact hr g v
    exact he ▸ ⟨model⟩

/-- Application to the unchanged C.1.32 consumer, with its sole remaining
source premise displayed on the literal ambient group LR. -/
theorem rankTwo_of_frattini_small (hsmall : FrattiniSmall L R) : RankTwoAlternatives L R :=
  h.rankTwo_of_g2_reconstruction e (reconstruction_of_frattini_small h e hsmall)

end G2Reconstruction

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

/-- Final reconstruction assembly, retaining both independent earlier-source
obligations. Neither conditional input is an unconditional source theorem. -/
theorem g2Reconstruction_of_distance_inputs
    (hd : G2Reconstruction.DistanceTwoInput.{u})
    (hc : G2Reconstruction.DistanceTwoComparisonInput.{u}) :
    G2ReconstructionInput.{u} KnownSimple.IsKnownSimple := by
  intro J _ _ L R h e
  exact G2Reconstruction.reconstruction_of_frattini_small h e
    (G2Reconstruction.frattini_small_of_distance_inputs h e hd hc)

/-- The unchanged rank-two classification consumes the assembled G₂ output. -/
theorem SmallMSPair.rankTwo_g2_of_distance_inputs
    (hd : G2Reconstruction.DistanceTwoInput.{u})
    (hc : G2Reconstruction.DistanceTwoComparisonInput.{u})
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    RankTwoAlternatives L R :=
  h.rankTwo_of_g2_reconstruction e (g2Reconstruction_of_distance_inputs hd hc G L R h e)

/-- The actual endpoint marking is proved. Only critical distance and the
reciprocal critical-image placement remain as earlier-source inputs. -/
theorem g2Reconstruction_of_distance_placement_inputs
    (hd : G2Reconstruction.DistanceTwoInput.{u})
    (hp : G2Reconstruction.Comparison.EndpointPlacementInput.{u}) :
    G2ReconstructionInput.{u} KnownSimple.IsKnownSimple :=
  g2Reconstruction_of_distance_inputs hd
    (G2Reconstruction.Comparison.distanceTwoComparison_of_endpoint_inputs
      G2Reconstruction.endpointModelInput_knownSimple hp)

/-- Apply the constructed whole endpoint quotient to the original small-MS
classifier; its two remaining geometric premises are retained explicitly. -/
theorem SmallMSPair.rankTwo_g2_of_distance_placement_inputs
    (hd : G2Reconstruction.DistanceTwoInput.{u})
    (hp : G2Reconstruction.Comparison.EndpointPlacementInput.{u})
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    RankTwoAlternatives L R :=
  h.rankTwo_of_g2_reconstruction e
    (g2Reconstruction_of_distance_placement_inputs hd hp G L R h e)

/-- Whole-core reconstruction with only the independent distance theorem explicit. -/
theorem g2Reconstruction_of_distance
    (hd : G2Reconstruction.DistanceTwoInput.{u}) :
    G2ReconstructionInput.{u} KnownSimple.IsKnownSimple :=
  g2Reconstruction_of_distance_inputs hd
    G2Reconstruction.Comparison.distanceTwoComparison_knownSimple

/-- The original small-MS classifier using the proved G₂ critical comparison. -/
theorem SmallMSPair.rankTwo_g2_of_distance
    (hd : G2Reconstruction.DistanceTwoInput.{u})
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    RankTwoAlternatives L R :=
  h.rankTwo_of_g2_reconstruction e (g2Reconstruction_of_distance hd G L R h e)


/-- Whole-core reconstruction after the remaining G₂ distance-four exclusion. -/
theorem g2Reconstruction_of_distanceFourExclusion
    (hfour : G2Reconstruction.DistanceTwo.DistanceFourExclusionInput.{u}) :
    G2ReconstructionInput.{u} KnownSimple.IsKnownSimple :=
  g2Reconstruction_of_distance (G2Reconstruction.distanceTwo_of_distanceFourExclusion hfour)

/-- The original classifier with the proved local-control and comparison families. -/
theorem SmallMSPair.rankTwo_g2_of_distanceFourExclusion
    (hfour : G2Reconstruction.DistanceTwo.DistanceFourExclusionInput.{u})
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    RankTwoAlternatives L R :=
  h.rankTwo_of_g2_reconstruction e (g2Reconstruction_of_distanceFourExclusion hfour G L R h e)

/-- The radius-group obstruction applied to the entire intrinsic block core.
Its remaining radius bound is retained explicitly for the source owner. -/
theorem g2Reconstruction_of_radiusTwoBound
    (hbound : G2Reconstruction.DistanceTwo.DistanceFour.RadiusTwoBoundInput.{u}) :
    G2ReconstructionInput.{u} KnownSimple.IsKnownSimple :=
  g2Reconstruction_of_distanceFourExclusion
    (G2Reconstruction.DistanceTwo.DistanceFour.distanceFourExclusion_of_radiusTwoBound hbound)

/-- Application of the radius-group calculation to the original small-MS classifier. -/
theorem SmallMSPair.rankTwo_g2_of_radiusTwoBound
    (hbound : G2Reconstruction.DistanceTwo.DistanceFour.RadiusTwoBoundInput.{u})
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    RankTwoAlternatives L R :=
  h.rankTwo_of_g2_reconstruction e (g2Reconstruction_of_radiusTwoBound hbound G L R h e)

/-- Whole-core reconstruction from the remaining fixed-derived natural-radius
construction. The invariant-form bound and its critical contradiction are proved. -/
theorem g2Reconstruction_of_fixedNaturalRadius
    (hnatural : G2Reconstruction.DistanceTwo.DistanceFour.FixedNaturalRadiusInput.{u}) :
    G2ReconstructionInput.{u} KnownSimple.IsKnownSimple :=
  g2Reconstruction_of_distanceFourExclusion
    (G2Reconstruction.DistanceTwo.DistanceFour.distanceFourExclusion_of_fixedNaturalRadius hnatural)

/-- The original SmallMSPair classifier consumes the whole radius calculation,
with its remaining fixed-derived and natural-marking construction explicit. -/
theorem SmallMSPair.rankTwo_g2_of_fixedNaturalRadius
    (hnatural : G2Reconstruction.DistanceTwo.DistanceFour.FixedNaturalRadiusInput.{u})
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    RankTwoAlternatives L R :=
  h.rankTwo_of_g2_reconstruction e (g2Reconstruction_of_fixedNaturalRadius hnatural G L R h e)

/-- The entire natural quotient is now recognized in the fixed-derived
branch. Only the nonfixed derived-radius exclusion remains to be supplied. -/
theorem g2Reconstruction_of_fixedRadius
    (hfixed : G2Reconstruction.DistanceTwo.DistanceFour.FixedRadiusInput.{u}) :
    G2ReconstructionInput.{u} KnownSimple.IsKnownSimple :=
  g2Reconstruction_of_distanceFourExclusion
    (G2Reconstruction.DistanceTwo.DistanceFour.distanceFourExclusion_of_fixedRadius hfixed)

/-- Apply the fixed-derived branch calculation to the original classifier,
retaining its remaining source obligation explicitly. -/
theorem SmallMSPair.rankTwo_g2_of_fixedRadius
    (hfixed : G2Reconstruction.DistanceTwo.DistanceFour.FixedRadiusInput.{u})
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    RankTwoAlternatives L R :=
  h.rankTwo_of_g2_reconstruction e (g2Reconstruction_of_fixedRadius hfixed G L R h e)


/-- Reconstruction from the last nonfixed-derived triple calculation in
MS93 (3.8). The fixed-derived argument and every recognition adapter are proved. -/
theorem g2Reconstruction_of_nonfixedCriticalEdge
    (htrip : G2Reconstruction.DistanceTwo.DistanceFour.NonfixedCriticalEdgeInput.{u}) :
    G2ReconstructionInput.{u} KnownSimple.IsKnownSimple :=
  g2Reconstruction_of_distanceFourExclusion
    (G2Reconstruction.DistanceTwo.DistanceFour.distanceFourExclusion_of_nonfixedCriticalEdge htrip)

/-- The literal SmallMSPair classifier consumes the source triple calculation
through distance-four exclusion and whole-core reconstruction. -/
theorem SmallMSPair.rankTwo_g2_of_nonfixedCriticalEdge
    (htrip : G2Reconstruction.DistanceTwo.DistanceFour.NonfixedCriticalEdgeInput.{u})
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    RankTwoAlternatives L R :=
  h.rankTwo_of_g2_reconstruction e (g2Reconstruction_of_nonfixedCriticalEdge htrip G L R h e)

/-- Uniform whole-core reconstruction in the G₂ row of C.1.32, including
elementary abelianness, centralization of O₂(L), and the actual natural
block-module quotient. No local critical-edge premise remains. -/
theorem g2Reconstruction_knownSimple : G2ReconstructionInput.{u} KnownSimple.IsKnownSimple :=
  g2Reconstruction_of_nonfixedCriticalEdge
    G2Reconstruction.DistanceTwo.DistanceFour.nonfixedCriticalEdge_knownSimple

/-- The original small MS-pair satisfies the literal rank-two alternative
in its G₂ row, with no Sylow requirement on R. -/
theorem SmallMSPair.rankTwo_g2_knownSimple
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    RankTwoAlternatives L R :=
  h.rankTwo_of_g2_reconstruction e (g2Reconstruction_knownSimple G L R h e)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
