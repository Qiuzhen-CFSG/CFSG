module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.OddCriticalActor
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Coordinates
/-!
# Odd critical actors in the original Baumann source

The opposite Z-layer of each actual critical path has odd image in the marked
six-letter quotient. The small forward image supplies a transposition. In the
large case, the reverse image has order at least four and acts quadratically,
which is impossible for an even subgroup of a conjugate point core.

This is the critical-actor input to the native source (5.12) argument, retaining
the literal Chapter 13 source, characteristic replacement and critical path.
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

/-- Every actual opposite critical image contains an odd permutation. -/
theorem sourceData_critical_opposite_image_not_le_alternating
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v≠1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B))) (e : Vertex r.radical)
      (_p : CriticalPath r.radical ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry
        (alpha r.radical) e),
      ¬ (((Z r.radical e).comap (embedM r.radical)).map
        ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).projection≤
          alternatingGroup (Fin 6)) := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p
  exact SymplecticSetup.SourceData.reducedSource_critical_opposite_image_not_le_alternating d0 hm r p
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
