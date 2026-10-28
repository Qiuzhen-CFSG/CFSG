module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CoordinatedChoices
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Coordinates
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.BlockChiefCount

/-!
# Coordinated symplectic choices in the original Chapter 13 source

The original chief-count obstruction excludes an alternating-six block.
Every characteristic replacement therefore supplies all the simultaneous
MS93 (5.5) choices: the same transported vertex and component element satisfy
both generation equations, both seed-center bounds, and alternative (c).
The witness carries the two vertices defining the subsequent A_delta set.

The later (5.7) backward-critical selection and terminal exclusion are still
separate obligations toward the core premise in OriginalBaumann.Control.
Source: Meierfrankenfeld--Stellmacher (1993), (5.5), pp.915--917, and p.919;
Aschbacher--Smith 13.7.4(1), through C.1.37.
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

theorem sourceData_coordinated_choices
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
      ∀ delta : Vertex r.radical, Adjacent r.radical delta (p.walk.getVert 1) →
        Nonempty (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).CoordinatedChoice
          p delta) := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p delta hdelta
  rcases SymplecticSetup.SourceData.reducedSource_block_or_coordinatedChoice d0 hm r p delta hdelta with hb | hg
  · exact (source_not_alternatingBlock d h hU hV hb).elim
  · exact hg
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
