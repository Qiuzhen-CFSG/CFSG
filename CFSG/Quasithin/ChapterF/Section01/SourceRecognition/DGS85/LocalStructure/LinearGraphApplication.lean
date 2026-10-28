module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearObstructionApplication

/-!
# Linear local conclusions on every edge of the reduced F1.11 graph

A common edge conjugator transports the complete (6.5) obstruction from
the two original base orientations to every adjacent pair. This constructs
the Chapter 8 earlier-local interface with its obstruction discharged,
and proves the (6.6) normal-center-product conclusion at every edge.
Both original linear quotient markings remain explicit; the completion
may be infinite and the two defining fields need not agree.

Source: DGS, Groups and Graphs (1985), (6.5)--(6.6), pp.121--123,
and the local input to Chapter 8, pp.132--133.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]

/-- Both linear markings give the actual 6.5 obstruction at every edge of the reduced graph. -/
theorem reduced_linear_graph_core_obstruction (h : HypothesisF11 L S)
    (e₀ : (L 0 ⧸ pCore 2 (L 0)) ≃* PSL(2,F))
    (e₁ : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (v w : Vertex (reducedFamily L S)) (hvw : (graph (reducedFamily L S)).Adj v w) :
    ¬ stabilizer (reducedFamily L S) v ≤ normalizer
      ((Q (reducedFamily L S) w ⊓ Q (reducedFamily L S) v : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
  have hb (j : Bool) : ¬ stabilizer (reducedFamily L S) (base (reducedFamily L S) j) ≤ normalizer
      ((Q (reducedFamily L S) (base (reducedFamily L S) (!j)) ⊓
        Q (reducedFamily L S) (base (reducedFamily L S) j) : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
    intro hh
    simp only [Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hh
    cases j
    · exact (reduced_linear_adjacent_core_obstruction h 1 e₀ e₁).1
        ((localEnlargement_le _).trans hh)
    · exact (reduced_linear_adjacent_core_obstruction h 0 e₁ e₀).1
        ((localEnlargement_le _).trans hh)
  obtain ⟨g,hv,hw⟩ := incident_common_translate (reducedFamily L S) hvw.2
  have ht : w.type = !v.type := Bool.eq_not_of_ne hvw.1.symm
  intro hh
  rw [←hv,←hw,Q_translate,Q_translate,stabilizer_translate,
    ←Subgroup.map_inf _ _ _ (MulAut.conj g).injective,←map_equiv_normalizer_eq] at hh
  have hh' := (map_le_map_iff_of_injective (MulAut.conj g).injective).mp hh
  rw [ht] at hh'
  exact hb v.type hh'

/-- The complete earlier-local interface on the linear reduced graph, with its 6.5 premise discharged. -/
@[expose] def reducedLinearEarlierLocalTheorems (h : HypothesisF11 L S)
    (e₀ : (L 0 ⧸ pCore 2 (L 0)) ≃* PSL(2,F))
    (e₁ : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    CommutingNontrivial.EarlierLocalTheorems (reducedFamily L S) :=
  reducedEarlierLocalTheorems h (reduced_linear_graph_core_obstruction h e₀ e₁)

/-- Source 6.6 at every reduced edge, retaining the original graph and all actual Sylows. -/
theorem reduced_linear_graph_normal_center_product (h : HypothesisF11 L S)
    (e₀ : (L 0 ⧸ pCore 2 (L 0)) ≃* PSL(2,F))
    (e₁ : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    {v w : Vertex (reducedFamily L S)} (hvw : (graph (reducedFamily L S)).Adj v w)
    (hn : stabilizer (reducedFamily L S) w ≤ normalizer
      (↑(Z (reducedFamily L S) v ⊔ Z (reducedFamily L S) w) : Set (G₀ L S))) :
    (∀ T : Sylow 2 (stabilizer (reducedFamily L S) v), Z (reducedFamily L S) v = omegaCenterIn
      ((T : Subgroup (stabilizer (reducedFamily L S) v)).map
        (stabilizer (reducedFamily L S) v).subtype)) ∧
      Z (reducedFamily L S) v ≤ Z (reducedFamily L S) w :=
  reduced_normal_center_product h hvw hn
    (reduced_linear_graph_core_obstruction h e₀ e₁ w v hvw.symm)
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
