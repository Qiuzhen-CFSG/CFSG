module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerOrientation
public import CFSG.Quasithin.ChapterF.Section05.ModelLocal
/-!
# Marked local comparison for the source vertex

The intrinsic product orientation on the source normalizer identifies its
vertex intersection with the first double-transposition centralizer. Composing
that orientation with the literal model product coordinates gives the local
isomorphism and its vertex-membership field. Agreement with the independently
constructed vertex map remains a separate F.5.7 compatibility condition.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour ExceptionalLocal
open OmegaSixThree.OrthogonalityGraph (modelSystem)
local notation "hn" => Nat.le_refl 1
local notation "S4" => Equiv.Perm (Fin 4)
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

noncomputable def sourceMarkedLocalComparison
    (e : H c i ≃* S4 × S4) : modelSystem.H ≃* H c i :=
  modelLocalEquiv.trans e.symm

theorem sourceMarkedLocalComparison_core
    (e : H c i ≃* S4 × S4) :
    (pCore 2 modelSystem.H).map
      (sourceMarkedLocalComparison c i e).toMonoidHom =
      (A c i true).subgroupOf (H c i) := by
  rw [pCore_map_iso,ExceptionalLocal.source_H_twoCore c i z h]

omit h [Finite G] in
theorem sourceMarkedLocalComparison_vertex
    (e : H c i ≃* S4 × S4)
    (he : ∀ a : H c i, (a : G) ∈ i.range ↔
      (e a).1 ∈ centralizer
        ({Theory.SpecificGroups.SymmetricSix.DuadCalculation.doubleSwap 0}:Set S4))
    (g : modelSystem.H) :
    (g : OmegaSixThree.omegaPlusSixThree) ∈ modelSystem.vertexGroup ↔
      (sourceMarkedLocalComparison c i e g : G) ∈ i.range := by
  rw [modelLocal_vertex_iff, he]
  change (modelLocalEquiv g).1 ∈ OmegaSixThree.TriangleLocal.square ↔
    (e (e.symm (modelLocalEquiv g))).1 ∈ _
  rw [e.apply_symm_apply]
  exact Iff.rfl

theorem exists_sourceMarkedLocalComparison
    (hp : ¬ H c i ≤ i.range) :
    ∃ e : H c i ≃* S4 × S4,
      (∀ a : H c i, (a : G) ∈ i.range ↔
        (e a).1 ∈ centralizer
          ({Theory.SpecificGroups.SymmetricSix.DuadCalculation.doubleSwap 0}:Set S4)) ∧
      (∀ g : modelSystem.H,
        (g : OmegaSixThree.omegaPlusSixThree) ∈ modelSystem.vertexGroup ↔
          (sourceMarkedLocalComparison c i e g : G) ∈ i.range) := by
  obtain ⟨e,he⟩ := ExceptionalLocal.exists_source_H_vertex_marking c i z h hp
  exact ⟨e,he,sourceMarkedLocalComparison_vertex c i e he⟩
end CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
