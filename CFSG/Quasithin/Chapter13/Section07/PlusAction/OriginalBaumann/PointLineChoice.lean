module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointLineChoice
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.ForwardKernel
/-!
# A moving-line choice with its generating edge in the original source

The noncentral moving-line conjugate and its generating neighboring kernel
are chosen simultaneously in the literal characteristic replacement.
The actual original chief count removes the alternating-block alternative.

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

/-- The actual original source supplies the same conjugator and generating
edge while retaining noncentrality on the opposite critical layer. -/
theorem sourceData_moving_line_edge_generator
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v≠1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B))) {c f : Vertex r.radical} (hc : color r.radical c=false),
      CriticalPair r.radical c f
        (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.exists_critical c hc) →
      ∀ H₁ : Subgroup (FreeAmalgam r.radical), H₁≤U r.radical c → H₁≠⊥ → Nat.card H₁≤2 →
      ∃ t : Vertex r.radical, Adjacent r.radical c t ∧
        Q r.radical t⊔Z r.radical f=stabilizer r.radical c ∧
        ∃ y∈stabilizer r.radical c,
          H₁.map (MulAut.conj y).toMonoidHom=U r.radical c⊓Z r.radical t ∧
          (stabilizer r.radical c⊓centralizer
            (H₁.map (MulAut.conj y).toMonoidHom:Set (FreeAmalgam r.radical)))⊔Z r.radical f=
              stabilizer r.radical c ∧
          ¬H₁.map (MulAut.conj y).toMonoidHom≤centralizer (Z r.radical f:Set (FreeAmalgam r.radical)) := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r c f hc hcrit H₁ hHU hH hcard
  exact (SymplecticSetup.SourceData.reducedSource_block_or_moving_line_edge_generator
    d0 hm r hc hcrit H₁ hHU hH hcard).resolve_left (source_not_alternatingBlock d h hU hV)
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
