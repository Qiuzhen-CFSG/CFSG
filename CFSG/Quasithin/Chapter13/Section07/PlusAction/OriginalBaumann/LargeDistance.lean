module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.LargeDistance
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.ForwardKernel
/-!
# Critical distance at most four in the original Baumann source

The native full point-core source excludes b > 4 by two prescribed backward
critical shifts and its nonzero fixed edge subgroup. The actual chief count
excludes the separate alternating-block alternative on every characteristic
replacement. No conditional critical-index or path-choice premise remains.

Source: MS93 (5.10), printed p.922, in the original Aschbacher--Smith
13.7.4(1) source through C.1.37.
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
local notation "X" => (L⊔(T:Subgroup G):Subgroup G)
local notation "LX" => L.subgroupOf X

/-- Every actual characteristic replacement has critical distance at most four. -/
theorem sourceData_criticalDistance_le_four
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v≠1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B))),
      ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical≤4 := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r
  exact (SymplecticSetup.SourceData.reducedSource_block_or_criticalDistance_le_four d0 hm r).resolve_left
    (source_not_alternatingBlock d h hU hV)
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
