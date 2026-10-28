module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.SelectedCritical
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.ForwardKernel
/-!
# The selected critical images in the original Baumann source

The actual chief count removes the alternating-block alternative. On the
same two selected critical paths, their middle commutator centralizes the
middle stabilizer and both critical images have order two. Native oddness
of every critical actor discharges the centralizer argument; no radius
quotient recognition or commutator-bound premise remains.

Source: MS93 (5.12)(2), printed pp.925--926, in the original
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
open BinaryMS.MS93.DistanceEight.PathCentrality
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
local notation "X" => (L⊔(T:Subgroup G):Subgroup G)
local notation "LX" => L.subgroupOf X

/-- Centrality and both image orders on the literal selected replacement paths. -/
theorem sourceData_selected_critical
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
      (_hb : 2<((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical)
      (m c e : Vertex r.radical)
      (p : CriticalPath r.radical ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry m c)
      (_q : CriticalPath r.radical ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry
        (alpha r.radical) e),
      (cosetGraph r.radical).dist m (alpha r.radical)≤2 →
      (cosetGraph r.radical).dist c (alpha r.radical)≤2 →
      (cosetGraph r.radical).dist c e<((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical →
      Q r.radical (p.walk.getVert 1)⊔Z r.radical e=stabilizer r.radical (alpha r.radical) →
      ⁅Z r.radical m,Z r.radical c⁆≤centralizer
        (stabilizer r.radical (alpha r.radical):Set (FreeAmalgam r.radical)) ∧
        (Q r.radical c).relIndex (Z r.radical m)=2 ∧
        (Q r.radical m).relIndex (Z r.radical c)=2 := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r hb m c e p q hm' hc hce hgen
  exact (SymplecticSetup.SourceData.reducedSource_block_or_selected_critical d0 hm r hb
    p q hm' hc hce hgen).resolve_left (source_not_alternatingBlock d h hU hV)
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
