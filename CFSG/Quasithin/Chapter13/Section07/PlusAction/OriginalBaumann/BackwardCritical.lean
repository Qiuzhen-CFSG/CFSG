module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.BackwardCritical
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.CoordinatedChoices
/-!
# The original large-image backward critical branch

The original Chapter 13 chief count excludes the alternating-block alternative.
The literal characteristic replacement therefore supplies the full point-core
marking and coordinated choice. In the large critical-image branch, the same
chosen backward vertex forms a critical pair with the second predecessor of
the original endpoint; no extra normalization or local-action premise remains.

This is the large-image branch of MS93 (5.7), printed p.919, used for
Aschbacher--Smith 13.7.4(1) through C.1.37. The small-image backward branch and
(5.8)--(5.12) remain obligations toward OriginalBaumann.Control's core premise.
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

theorem sourceData_large_backward_critical
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
        ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry (alpha r.radical) e)
      (delta : Vertex r.radical), Adjacent r.radical delta (p.walk.getVert 1) →
      2 < ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical →
      1 < (B r.radical (alpha r.radical)
        (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _)).relIndex
          (U r.radical delta) →
      4 ≤ (Q r.radical e).relIndex (Z r.radical (alpha r.radical)) →
      ∃ c : ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).CoordinatedChoice p delta,
        CriticalPair r.radical c.alpha1 (p.walk.getVert (p.walk.length-2))
          (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.exists_critical
            c.alpha1 c.back_color) := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p delta hdelta hb hindex hlarge
  obtain ⟨c⟩ := sourceData_coordinated_choices d h hU hV v hv hm r p delta hdelta
  refine ⟨c,?_⟩
  rcases SymplecticSetup.SourceData.reducedSource_block_or_large_backward_critical
    d0 hm r c hb hindex hlarge with hblock | hcrit
  · exact (source_not_alternatingBlock d h hU hV hblock).elim
  · exact hcrit
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
