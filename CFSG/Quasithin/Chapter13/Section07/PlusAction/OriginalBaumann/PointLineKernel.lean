module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointLineKernel
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.ForwardKernel
/-!
# Point-line edge kernels for the original Baumann source

A nonzero moving line in an adjacent edge layer determines the entire edge
kernel. Its centralizer in the vertex stabilizer normalizes that kernel.
The actual source's chief count excludes the alternating-block alternative.

Source: MS93 (5.9), printed pp.920--921, for the original
Aschbacher--Smith 13.7.4(1) source through C.1.37.
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

/-- The actual original source's moving line determines and normalizes its
literal adjacent edge kernel. -/
theorem sourceData_point_line_kernel
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v≠1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (_hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B))) (a t : Vertex r.radical),
      color r.radical a=false → Adjacent r.radical a t →
      ∀ H₁ : Subgroup (FreeAmalgam r.radical), H₁≤U r.radical a⊓Z r.radical t → H₁≠⊥ →
        (stabilizer r.radical a⊓centralizer (H₁:Set (FreeAmalgam r.radical))≤
          normalizer (Q r.radical t:Set (FreeAmalgam r.radical))) ∧
        ∀ t' : Vertex r.radical, Adjacent r.radical a t' → H₁≤Z r.radical t' →
          Q r.radical t'=Q r.radical t := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r
  exact (SymplecticSetup.SourceData.reducedSource_block_or_point_line_kernel d0 hm r).resolve_left
    (source_not_alternatingBlock d h hU hV)
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
