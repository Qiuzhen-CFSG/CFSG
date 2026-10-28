module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.SelectedChain
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.ForwardKernel
/-!
# Prescribed small backward paths in the original Baumann source

At critical distance four, every supplied coordinated choice yields its
prescribed backward critical path, with its first three vertices retained.
Both critical images of this path have order two. The source chief count
excludes the separate alternating-block alternative of the replacement.

This is the selected-smallness input to MS93 (5.12)(3), using the actual
Chapter 13 quotient maps and the same coordinated choice as that consumer.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
open CFSG.Quasithin.ChapterC CFSG.Quasithin.ChapterC.NaturalSixControl
open Section08.SourceCompletion Section05.PlaneGeometry
open Section08.TransvectionRecognition.Component.ModelExtension
open BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open BinaryMS.MS93.DistanceEight.PathCentrality
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
local notation "X" => (L⊔(T:Subgroup G):Subgroup G)
local notation "LX" => L.subgroupOf X

/-- The actual source supplies the selected backward path and its two
order-two critical images on the same coordinated choice. -/
theorem sourceData_prescribed_small_backward_path
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v≠1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B)))
      (_hb : ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical=4)
      (e : Vertex r.radical)
      (p : CriticalPath r.radical ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry
        (alpha r.radical) e)
      (c : ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).CoordinatedChoice p (p.walk.getVert 2)),
    ∃ q : CriticalPath r.radical ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry
        c.alpha1 (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 1=c.beta1 ∧ q.walk.getVert 2=alpha r.radical ∧
      q.walk.getVert 3=p.walk.getVert 1 ∧
      (Q r.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z r.radical c.alpha1)=2 ∧
      (Q r.radical c.alpha1).relIndex (Z r.radical (p.walk.getVert (p.walk.length-2)))=2 := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r hb e p c
  exact (SymplecticSetup.SourceData.reducedSource_block_or_prescribed_small_backward_path d0 hm r hb p c).resolve_left
    (source_not_alternatingBlock d h hU hV)
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
