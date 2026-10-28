module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.BackwardEscape
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.CoordinatedChoices

/-!
# Unconditional backward escape for the original Baumann source

The original chief count excludes the alternating-block alternative. The
literal characteristic replacement therefore supplies source (5.8): an
eligible coordinated backward critical pair, radius escape, and the forward
Baumann index at least two. The universal escape clause is retained for the
subsequent critical-distance argument on this same reduced source.

Source: MS93 (5.8), printed pp.919--920; Aschbacher--Smith C.1.37 and
13.7.4(1). This discharges the previous index-greater-than-two selection
premise. The later core equality required by OriginalBaumann.Control is
not asserted here.
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
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
local notation "X" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "LX" => L.subgroupOf X

/-- The exact original source has unconditional backward escape and the
forward index bound, without a separate geometric or model premise. -/
theorem sourceData_backward_escape
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v ≠ 1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX ⊔ d0.B))
        (d0.B.subgroupOf (LX ⊔ d0.B))) {e : Vertex r.radical}
      (p : DistanceEight.PathCentrality.CriticalPath r.radical
        ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry (alpha r.radical) e),
      2 < ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical →
      (∃ delta, ∃ c : ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).CoordinatedChoice p delta,
        Adjacent r.radical delta (p.walk.getVert 1) ∧
        1 < (B r.radical (alpha r.radical) (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _)).relIndex (U r.radical delta) ∧
        CriticalPair r.radical c.alpha1 (p.walk.getVert (p.walk.length-2))
          (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.exists_critical c.alpha1 c.back_color)) ∧
      (¬ BinaryMS.MS93.V r.radical (alpha r.radical) ≤ Q r.radical (p.walk.getVert (p.walk.length-2))) ∧
      2 ≤ (B r.radical (alpha r.radical) (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _)).relIndex
        (U r.radical (p.walk.getVert 2)) ∧
      Factorization.CriticalEscape r.radical ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p hb
  rcases SymplecticSetup.SourceData.reducedSource_block_or_backward_escape d0 hm r p hb with hblock | hescape
  · exact (source_not_alternatingBlock d h hU hV hblock).elim
  · exact hescape

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
