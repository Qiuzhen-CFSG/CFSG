module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ShiftedForwardConfiguration
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.NoncentralSeedChoice

/-!
# The shifted forward configuration on the original Baumann source

The original chief-count obstruction removes the alternating-block branch
of the exact characteristic replacement. Its actual forward index-two
hypothesis therefore supplies the same shifted endpoint, conjugator, line,
normal span and kernel, with both line-centralizer spans in the old endpoint
kernel. This is the middle paragraph of MS93 (5.9), printed pp.920--921,
toward Aschbacher--Smith 13.7.4(1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterC.NaturalSixControl
open Section08.SourceCompletion Section05.PlaneGeometry
open Section08.TransvectionRecognition.Component.ModelExtension
open BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open DistanceEight.PathCentrality
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
local notation "X" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "LX" => L.subgroupOf X

/-- The original natural-six source supplies both actual kernel placements. -/
theorem sourceData_shifted_forward_configuration
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v≠1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B))) {e : Vertex r.radical}
      (p : CriticalPath r.radical
        ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry (alpha r.radical) e)
      (hb : 4<((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical),
      (B r.radical (alpha r.radical)
        (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _)).relIndex
          (U r.radical (p.walk.getVert 2))=2 →
      ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).ShiftedForwardConfiguration hb p := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p hb hindex
  rcases SymplecticSetup.SourceData.reducedSource_block_or_shifted_forward_configuration
    d0 hm r p hb hindex with hblock | hconfig
  · exact (source_not_alternatingBlock d h hU hV hblock).elim
  · exact hconfig

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
