module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.NonquadraticEdge
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Coordinates
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.BlockChiefCount

/-!
# The original Baumann source has no quadratic full edge action

The original chief-count obstruction rules out the alternating block. On every
characteristic replacement, both the edge kernel and the actual maximal-offender
join therefore have nonzero double commutator on the natural moving layer.
All groups and maps are those of the original Chapter 13 source.

This is the terminal nonquadratic input for the MS93 (5.10), (5.12) path
argument used in Aschbacher--Smith 13.7.4(1) through C.1.37. The geometric step
forcing quadraticity remains with that argument.
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

/-- No full edge kernel or maximal-offender join of the actual source acts
quadratically on its natural moving layer. -/
theorem sourceData_nonquadratic_edges
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v ≠ 1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (_hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B))) (a t : Vertex r.radical),
      color r.radical a=false → Adjacent r.radical a t →
      ⁅⁅U r.radical a,Q r.radical t⁆,Q r.radical t⁆≠⊥ ∧
      ⁅⁅U r.radical a,SymplecticSetup.edgeOffenderJoin a t⁆,
        SymplecticSetup.edgeOffenderJoin a t⁆≠⊥ := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r a t ha hat
  rcases SymplecticSetup.SourceData.reducedSource_block_or_nonquadratic_edges d0 hm r with hb|hn
  · exact (source_not_alternatingBlock d h hU hV hb).elim
  · exact hn a t ha hat

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
