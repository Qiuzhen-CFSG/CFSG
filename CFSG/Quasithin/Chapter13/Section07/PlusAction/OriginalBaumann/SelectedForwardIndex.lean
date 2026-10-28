module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.SelectedForwardIndex
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Coordinates
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.BlockChiefCount

/-!
# Forward index two in the original distance-four source

Every actual characteristic replacement at critical distance four has forward
moving-layer Baumann index two. Its selected backward smallness is supplied
by the same native coordinated choice, and the original chief count excludes
the separate alternating-block alternative. No selected-image premise remains.

Source: MS93 (5.12)(3), in the original Chapter 13 Baumann source.
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

/-- The literal reduced source has forward Baumann index two at distance four. -/
theorem sourceData_forward_index_eq_two_of_distance_four
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v ≠ 1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B))) (e : Vertex r.radical)
      (p : DistanceEight.PathCentrality.CriticalPath r.radical
        ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry (alpha r.radical) e),
      ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical=4 →
      (B r.radical (alpha r.radical)
        (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _)).relIndex
        (U r.radical (p.walk.getVert 2))=2 := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p hb
  rcases SymplecticSetup.SourceData.reducedSource_block_or_forward_index_eq_two_of_distance_four
    d0 hm r hb p with hblock|hk
  · exact (source_not_alternatingBlock d h hU hV hblock).elim
  · exact hk

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
