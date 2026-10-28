module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.CommutingTrivialFullCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralEquivalencesSource

/-!
# Chapter 9 from the proved full-catalogue Chapter 8 theorem

Zero displacement at the original critical pair gives 8.6(c) at the reversed
pair. The all-catalogue theorem supplies the actual reverse starting linear
quotient and distance three. It therefore discharges Chapter 9's Chapter 8
premise and proves both adjacent fields have order two.

No reverse-recognition callback, terminal-rank restriction, supplied field
marking or binary-model witness remains. The full source catalogue is
retained, including the dihedral alternatives;
the required representation-model witnesses are derived internally.
Source: DGS, *Groups and Graphs* (1985), 8.6, 9.2 and 9.10,
printed pp.139,142,147–150.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "Γ" => Reduction.reducedFamily L S₀

/-- The proved general 8.6 theorem discharges the actual Chapter 9 reverse premise. -/
theorem reduced_critical_fields_two_from_chapterEight
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ}
    (hc : IsCriticalPair Γ a a') (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥) :
    b Γ = 3 ∧
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
        (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
        Nat.card F = 2 ∧ Nat.card K = 2 ∧
          Nonempty ((graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F)) ∧
          Nonempty ((graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃* SL(2,K)) := by
  apply reduced_critical_fields_two_from_full_catalogue h models hc hab hd hb hcomm htriv
    ?_
  intro z hz hzc hzcomm hrev
  have hd' : (graph Γ).dist a' beta + 1 = b Γ := by rwa [SimpleGraph.dist_comm]
  have hi : ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1 ⊓ Q Γ a'⁆ = ⊥ := by
    rw [commutator_comm]
    exact bot_unique ((commutator_mono le_rfl inf_le_left).trans htriv.le)
  obtain ⟨hb3,_,hn⟩ := CommutingNontrivial.reduced_terminal_intersection_natural
    h models hzc hz hd' hb hzcomm hrev hi
  obtain ⟨K,_,_,_,he⟩ := CommutingNontrivial.source_natural_center_linear_quotient
    (Reduction.reduced_triple h) (Reduction.reducedFullEarlierLocalTheorems h) z hn
  exact ⟨K,inferInstance,inferInstance,inferInstance,hb3,he⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
