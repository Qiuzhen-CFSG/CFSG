module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardLineAll
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Coordinates
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.BlockChiefCount

/-!
# The original source forward commutator lies in its fixed core

The actual characteristic replacement has its forward hyperplane-kernel
commutator in the starting fixed core whenever the critical distance exceeds
two and the forward moving-layer Baumann index is at most two. The original
chief count excludes the alternating-block alternative. This retains the
literal source maps and removes the earlier strict distance-four restriction
from the line argument needed in MS93 (5.12).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
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

/-- The forward hyperplane-kernel commutator of the literal replacement lies in its fixed core. -/
theorem sourceData_forward_fixed_line_of_two_lt
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
      2 < ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical →
      (B r.radical (alpha r.radical)
        (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _)).relIndex
        (U r.radical (p.walk.getVert 2)) ≤ 2 →
      (let T₀ := Q r.radical (alpha r.radical) ⊓ centralizer
         (U r.radical (p.walk.getVert 2) ⊓ B r.radical (alpha r.radical)
           (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _) :
             Set (FreeAmalgam r.radical))
       ⁅U r.radical (p.walk.getVert 2),T₀⁆ ≤ fixedCore r.radical (alpha r.radical)) := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p hb hindex
  rcases SymplecticSetup.SourceData.reducedSource_block_or_forward_fixed_line_of_two_lt
    d0 hm r p hb hindex with hblock|hk
  · exact (source_not_alternatingBlock d h hU hV hblock).elim
  · exact hk

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
