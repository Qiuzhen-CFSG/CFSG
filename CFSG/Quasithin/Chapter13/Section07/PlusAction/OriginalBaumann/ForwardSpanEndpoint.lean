module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpanEndpoint
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.ForwardSpanAll
/-!
# The critical endpoint action in the original Baumann source

The original chief count eliminates the alternating-block alternative.
Every opposite critical seed element fixes a subgroup of index at most two
on the literal terminal central quotient P/Z(P). This is the endpoint
transvection input of MS93 (5.12), printed p.927, for source13.7.4(1).
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
open CFSG.Quasithin.ChapterC CFSG.Quasithin.ChapterC.NaturalSixControl
open Section08.SourceCompletion Section05.PlaneGeometry
open Section08.TransvectionRecognition.Component.ModelExtension
open BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
local notation "X" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "LX" => L.subgroupOf X

open DistanceEight.PathCentrality

theorem sourceData_forward_span_endpoint
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v ≠ 1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B))) {e : Vertex r.radical}
      (p : CriticalPath r.radical
        ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry (alpha r.radical) e),
      ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical=4 →
      ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).ForwardSpanEndpointData p := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p hb
  exact (SymplecticSetup.SourceData.reducedSource_block_or_forward_span_endpoint d0 hm r p hb).resolve_left
    (source_not_alternatingBlock d h hU hV)
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
