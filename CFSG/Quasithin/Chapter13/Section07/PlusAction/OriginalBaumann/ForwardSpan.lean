module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpan
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Coordinates
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.BlockChiefCount

/-!
# The normal forward span in the original Baumann source

In the literal characteristic replacement, the hyperplane-kernel commutator
line centralizes the starting stabilizer and bounds the commutator of the
normal forward Z-span. The original chief-count obstruction discharges the
block alternative. This is the normal generation input to MS93 (5.9), printed
pp.920--921, used through Aschbacher--Smith C.1.37 and 13.7.4(1).
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

/-- Normal generation preserves the actual forward commutator line. -/
theorem sourceData_forward_span
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
      4 < ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical →
      (B r.radical (alpha r.radical)
        (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _)).relIndex
        (U r.radical (p.walk.getVert 2)) ≤ 2 →
      let T₀ := Q r.radical (alpha r.radical) ⊓ centralizer
        (U r.radical (p.walk.getVert 2) ⊓ B r.radical (alpha r.radical)
          (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _) :
            Set (FreeAmalgam r.radical))
      let H₀ := ⁅U r.radical (p.walk.getVert 2),T₀⁆
      H₀ ≤ centralizer (stabilizer r.radical (alpha r.radical) : Set (FreeAmalgam r.radical)) ∧
        ⁅DistanceEight.PathCentrality.localZSpan r.radical (p.walk.getVert 2) (alpha r.radical),T₀⁆ ≤ H₀ := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p hb hindex
  rcases SymplecticSetup.SourceData.reducedSource_block_or_forward_span
    d0 hm r p hb hindex with hblock|hk
  · exact (source_not_alternatingBlock d h hU hV hblock).elim
  · exact hk

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
