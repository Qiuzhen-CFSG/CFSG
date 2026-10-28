module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ShiftedSeedChoice
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.NoncentralSeedChoice

/-!
# Shifted line choices for the original Baumann source

The original chief count removes the alternating-block alternative. For
every actual critical path of length greater than four, a nonzero moving
line at its second vertex has a shifted critical endpoint and a conjugator
there. The conjugate line's local centralizer generates with the endpoint
Z-layer, and that same layer moves the same conjugate line.

The literal source subgroup, quotient marking, characteristic replacement
and conjugation maps are retained. This supplies MS93 (5.9)'s second starred
choice, printed pp.920--922, toward Aschbacher--Smith 13.7.4(1).
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
open DistanceEight.PathCentrality
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
local notation "X" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "LX" => L.subgroupOf X

/-- The second starred choice, on the original natural-six source data. -/
theorem sourceData_shifted_seed_choice
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
      (p : CriticalPath r.radical
        ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry (alpha r.radical) e)
      (hb : 4 < ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical)
      (A : Subgroup (FreeAmalgam r.radical)),
      A ≤ U r.radical (p.walk.getVert 2) → A ≠ ⊥ → Nat.card A ≤ 2 →
      ∃ f, color r.radical f=false ∧ (cosetGraph r.radical).dist e f=2 ∧
        CriticalPair r.radical (p.walk.getVert 2) f
          (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.exists_critical _
            ((p.vertex_color (by rw [p.length_eq_b]; omega)).mpr (by decide))) ∧
        ∃ y ∈ stabilizer r.radical (p.walk.getVert 2),
          (stabilizer r.radical (p.walk.getVert 2) ⊓
            centralizer (A.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam r.radical))) ⊔
              Z r.radical f = stabilizer r.radical (p.walk.getVert 2) ∧
          ¬ A.map (MulAut.conj y).toMonoidHom ≤ centralizer (Z r.radical f : Set (FreeAmalgam r.radical)) := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p hb A hAU hA hc
  rcases SymplecticSetup.SourceData.reducedSource_block_or_shifted_seed_choice
    d0 hm r p hb A hAU hA hc with hblock | hchoice
  · exact (source_not_alternatingBlock d h hU hV hblock).elim
  · exact hchoice

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
