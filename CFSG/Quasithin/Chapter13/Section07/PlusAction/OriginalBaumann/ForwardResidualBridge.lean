module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardResidualBridge
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.ForwardMovedSpanNatural
/-!
# Residual containment in the selected endpoint orbit

In the actual Chapter13 characteristic replacement, the endpoint orbit and
its index-two moving layer give [Q_alpha,L_alpha] inside U_alpha [P,L_alpha].
The natural central quotient supplies the required moved subgroup, and the
odd endpoint action contracts the remaining two-residual quotient. The
original chief count removes the alternating-block alternative.

Source: MS93 (3.10)(i) and the terminal paragraph of (5.12), pp.880 and927.
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

theorem sourceData_core_commutator_le_moving_sup_forward_moved_span_of_orbit
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
      ∀ (g : FreeAmalgam r.radical), g∈stabilizer r.radical (p.walk.getVert 2) →
      act r.radical g (alpha r.radical)=e →
      (B r.radical (p.walk.getVert 2)
        (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _)).relIndex
          (U r.radical e)≤2 →
      ⁅Q r.radical (alpha r.radical),Ltilde r.radical (alpha r.radical)⁆≤
        U r.radical (alpha r.radical)⊔SymplecticSetup.forwardMovedSpan r.radical (p.walk.getVert 2) := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p hb g hg he hindex
  exact (SymplecticSetup.SourceData.reducedSource_block_or_core_commutator_le_moving_sup_forward_moved_span_of_orbit
    d0 hm r p hb g hg he hindex).resolve_left
    (source_not_alternatingBlock d h hU hV)
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
