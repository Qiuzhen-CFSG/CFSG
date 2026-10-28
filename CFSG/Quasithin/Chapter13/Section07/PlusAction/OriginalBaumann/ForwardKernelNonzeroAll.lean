module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardKernelNonzeroAll
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.ForwardKernel

/-!
# Nonzero forward kernels including the original distance-four source

The original chief-count exclusion removes the alternating-block branch.
The actual forward-kernel commutator is therefore nonzero whenever its
Baumann index is two and the critical distance exceeds two. This is the
nonzero line input to MS93 (5.9), printed p.920, available also for the
terminal distance-four case in the original 13.7.4(1) source.
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

/-- The actual Chapter 13 forward-kernel commutator is nonzero in the
index-two contrary case, without a separate model or nonvanishing premise. -/
theorem sourceData_forward_kernel_nonzero_of_two_lt
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v≠1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B))) {e : Vertex r.radical}
      (p : DistanceEight.PathCentrality.CriticalPath r.radical
        ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry (alpha r.radical) e),
      2<((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical →
      (B r.radical (alpha r.radical)
        (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _)).relIndex
          (U r.radical (p.walk.getVert 2))=2 →
      (let T₀ := Q r.radical (alpha r.radical) ⊓ centralizer
        (U r.radical (p.walk.getVert 2) ⊓ B r.radical (alpha r.radical)
          (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _) :
            Set (FreeAmalgam r.radical))
       ⁅U r.radical (p.walk.getVert 2),T₀⁆≠⊥) := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p hb hindex
  rcases SymplecticSetup.SourceData.reducedSource_block_or_forward_kernel_nonzero_of_two_lt
    d0 hm r p hb hindex with hblock|hn
  · exact (source_not_alternatingBlock d h hU hV hblock).elim
  · exact hn

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
