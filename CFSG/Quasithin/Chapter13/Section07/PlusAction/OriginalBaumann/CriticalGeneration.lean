module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CriticalGeneration
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Coordinates
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.BlockChiefCount

/-!
# Critical generating neighbors in the original Chapter 13 source

The actual sourceData excludes an alternating-six block. Applying the
symplectic generation alternative therefore supplies the chosen graph
neighbor and its seed-centralizer bound for every characteristic replacement
and every critical path. The statement keeps the original quotient maps and
requires no extra full-image or actor hypothesis.

This is the source application of the generation and centralizer steps in
Meierfrankenfeld--Stellmacher (1993), (5.5)(a,b), printed pp.915--917,
toward Aschbacher--Smith 13.7.4(1). The later backward critical selection and
terminal exclusion remain distinct mathematical obligations.
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

theorem sourceData_critical_generating_neighbor
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
        ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry (alpha r.radical) e),
      ∃ t : Vertex r.radical, Adjacent r.radical (alpha r.radical) t ∧
        Q r.radical t ⊔ Z r.radical e = stabilizer r.radical (alpha r.radical) ∧
        Z r.radical (p.walk.getVert 1) ⊓ centralizer (Q r.radical t : Set (FreeAmalgam r.radical)) ≤
          centralizer (stabilizer r.radical (alpha r.radical) : Set (FreeAmalgam r.radical)) := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p
  rcases SymplecticSetup.SourceData.reducedSource_block_or_generating_neighbor d0 hm r p with hb | hg
  · exact (source_not_alternatingBlock d h hU hV hb).elim
  · exact hg
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
