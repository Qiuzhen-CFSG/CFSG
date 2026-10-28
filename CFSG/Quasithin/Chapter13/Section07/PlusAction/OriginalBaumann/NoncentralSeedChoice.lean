module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.NoncentralSeedChoice
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.CriticalGeneration

/-!
# Noncentral seed choices in the original Baumann source

The original chief count excludes the alternating-block alternative. Every
actual characteristic replacement therefore splits its Z-layer into its
natural moving layer and its central intersection. An element outside the
fixed core has a component conjugate whose local centralizer generates with
the opposite critical layer and which is moved by that layer. Both clauses
use the same conjugator and the original graph action.

This supplies the starred choice in MS93 (5.9), printed pp.920--922, toward
Aschbacher--Smith 13.7.4(1). The remaining radius geometry and final core
equality are separate source obligations.
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

/-- The original Chapter 13 source supplies both clauses of the same seed choice. -/
theorem sourceData_noncentral_seed_generator
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
      (_p : DistanceEight.PathCentrality.CriticalPath r.radical
        ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry (alpha r.radical) e),
      (Z r.radical (alpha r.radical) = U r.radical (alpha r.radical) ⊔
        (Z r.radical (alpha r.radical) ⊓
          (center (stabilizer r.radical (alpha r.radical))).map
            (stabilizer r.radical (alpha r.radical)).subtype)) ∧
      ∀ z ∈ Z r.radical (alpha r.radical), z ∉ fixedCore r.radical (alpha r.radical) →
      ∃ g ∈ Ltilde r.radical (alpha r.radical),
        (stabilizer r.radical (alpha r.radical) ⊓
          centralizer ({g*z*g⁻¹}:Set (FreeAmalgam r.radical))) ⊔ Z r.radical e =
            stabilizer r.radical (alpha r.radical) ∧
        g*z*g⁻¹ ∉ centralizer (Z r.radical e : Set (FreeAmalgam r.radical)) := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p
  rcases SymplecticSetup.SourceData.reducedSource_block_or_noncentral_seed_generator
    d0 hm r p with hb | hg
  · exact (source_not_alternatingBlock d h hU hV hb).elim
  · exact hg

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
