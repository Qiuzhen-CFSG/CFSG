module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.DistanceFour.CriticalTriple
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.ExceptionalCore
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# Whole-core reconstruction for the exceptional root-eight MS pair

The actual central-omega action supplies the natural endpoint marking.
The reciprocal critical-image comparison proves the Frattini bound at
critical distance two. The local-control and critical-triple arguments
exclude every larger distance, completing MS93 (3.3), (3.6), and (3.8)
for the exceptional MS2(b) pair. No distance or module bound is assumed.

The proof adapts the completed Chapter15 MarkedMS.G2Reconstruction family;
only its edge two-group and core-containment inputs are changed. Its
original MS2(a) API is preserved. Source: AS C.1.31--32, pp.135--136;
MS93 (3.6), p.870, (3.8), pp.877--879, Main Theorem (10).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

/-- The original exceptional pair satisfies the whole-core Frattini bound. -/
theorem frattini_small (h : Pair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    FrattiniSmall L R :=
  frattini_small_of_distanceFourExclusion
    (DistanceTwo.DistanceFour.distanceFourExclusion_of_nonfixedCriticalEdge
      DistanceTwo.DistanceFour.nonfixedCriticalEdge_knownSimple) h e

/-- The literal relative component is a G₂ block, including its whole
intrinsic commutator module rather than only the initial omega layer. -/
theorem block (h : Pair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    IsG2TwoBlock L := by
  obtain ⟨_,hs,hm⟩ := h.block_of_frattini_small (frattini_small h e)
  let eK : L.subgroupOf (L ⊔ R) ≃* L := subgroupOfEquivOfLe le_sup_left
  exact ⟨hs.of_mulEquiv eK,IsLinearBlockModel.of_mulEquiv hm eK⟩
end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction
