module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveReplacement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSpecialUnitaryEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.MixedLinearApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NonlinearSmallGraphApplication

/-!
# Unconditional adjacent-core obstruction on the original reduced graph

The faithful replacement-section argument handles PSU₃(2) even when its
actual enlargement has order 144. Together with the existing linear,
Suzuki, dihedral and special-unitary branches, this proves both clauses
of DGS 6.5 and the 6.6 center product at every reduced edge under the
original Hypothesis F.1.1. Both mixed orientations and all field degrees
are retained. The Chapter 8 earlier-local interface now has no extra
obstruction or order-exclusion premise.

This does not identify the order-144 enlargement as a rank-one model.
The original 6.1 catalogue and the remaining 6.4--6.8/source assembly
obligations remain separate. Source: DGS, Groups and Graphs (1985),
6.5--6.6, pp.121--123; Aschbacher--Smith F.1.1 and F.1.9.
-/

open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Both obstructions at the exact reduced endpoints, including both degree-one unitary forms. -/
theorem reduced_adjacent_core_obstruction (h : HypothesisF11 L S) (i : Fin 2) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    (¬ localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set (G₀ L S))) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 := by
  cases h.quotient (other i) with
  | linear n hn hm =>
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hc)
    exact reduced_linear_obstruction_unrestricted_opposite h i e
  | suzuki m hm => exact reduced_nonlinear_adjacent_core_obstruction h i (Or.inl ⟨m,hm⟩)
  | projective_unitary n hn hm =>
    by_cases he : n = 1
    · subst n
      exact reduced_small_projective_adjacent_core_obstruction h i (by simpa using hm)
    · exact reduced_nonlinear_adjacent_core_obstruction h i (Or.inr (Or.inl ⟨n,by omega,hm⟩))
  | special_unitary n hn hm =>
    by_cases he : n = 1
    · subst n
      exact reduced_small_unitary_enlargement_obstruction h i
        (Or.inr (original_small_special_enlarged_marking h (other i) (by simpa using hm)))
    · exact reduced_nonlinear_adjacent_core_obstruction h i (Or.inr (Or.inr (Or.inl ⟨n,by omega,hm⟩)))
  | dihedral hm => exact reduced_nonlinear_adjacent_core_obstruction h i (Or.inr (Or.inr (Or.inr hm)))

/-- The nonnormality clause of 6.5 at every edge, including both degree-one unitary forms. -/
theorem reduced_graph_core_obstruction (h : HypothesisF11 L S)
    (v w : Vertex (reducedFamily L S)) (hvw : (graph (reducedFamily L S)).Adj v w) :
    ¬ stabilizer (reducedFamily L S) v ≤ normalizer
      ((Q (reducedFamily L S) w ⊓ Q (reducedFamily L S) v : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
  have hb (j : Bool) : ¬ stabilizer (reducedFamily L S) (base (reducedFamily L S) j) ≤ normalizer
      ((Q (reducedFamily L S) (base (reducedFamily L S) (!j)) ⊓
        Q (reducedFamily L S) (base (reducedFamily L S) j) : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
    intro hh
    simp only [Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hh
    cases j
    · exact (reduced_adjacent_core_obstruction h 1).1
        ((localEnlargement_le _).trans hh)
    · exact (reduced_adjacent_core_obstruction h 0).1
        ((localEnlargement_le _).trans hh)
  obtain ⟨g,hv,hw⟩ := incident_common_translate (reducedFamily L S) hvw.2
  have ht : w.type = !v.type := Bool.eq_not_of_ne hvw.1.symm
  intro hh
  rw [←hv,←hw,Q_translate,Q_translate,stabilizer_translate,
    ←Subgroup.map_inf _ _ _ (MulAut.conj g).injective,←map_equiv_normalizer_eq] at hh
  have hh' := (map_le_map_iff_of_injective (MulAut.conj g).injective).mp hh
  rw [ht] at hh'
  exact hb v.type hh'

/-- The second clause of 6.5 uses the closure under the full neighboring stabilizer at every edge. -/
theorem reduced_graph_core_not_sylow (h : HypothesisF11 L S)
    (v w : Vertex (reducedFamily L S)) (hvw : (graph (reducedFamily L S)).Adj v w) :
    ¬ ∃ T : Sylow 2 (conjugateSpanBy (Q (reducedFamily L S) w) (stabilizer (reducedFamily L S) v)),
      (T : Subgroup (conjugateSpanBy (Q (reducedFamily L S) w) (stabilizer (reducedFamily L S) v))).map
        (conjugateSpanBy (Q (reducedFamily L S) w) (stabilizer (reducedFamily L S) v)).subtype =
          Q (reducedFamily L S) w := by
  intro hs
  exact reduced_graph_core_obstruction h v w hvw
    (graph_core_inter_normal_of_sylow (reduced_triple h) hvw hs)

/-- The actual earlier-local interface, allowing mixed families and unequal endpoint fields. -/
@[expose] def reducedFullEarlierLocalTheorems (h : HypothesisF11 L S) :
    CommutingNontrivial.EarlierLocalTheorems (reducedFamily L S) :=
  reducedEarlierLocalTheorems h (reduced_graph_core_obstruction h)

/-- Source 6.6 at every reduced edge, retaining the original graph and all actual Sylows. -/
theorem reduced_graph_center_product (h : HypothesisF11 L S)
    {v w : Vertex (reducedFamily L S)} (hvw : (graph (reducedFamily L S)).Adj v w)
    (hn : stabilizer (reducedFamily L S) w ≤ normalizer
      (↑(Z (reducedFamily L S) v ⊔ Z (reducedFamily L S) w) : Set (G₀ L S))) :
    (∀ T : Sylow 2 (stabilizer (reducedFamily L S) v), Z (reducedFamily L S) v = omegaCenterIn
      ((T : Subgroup (stabilizer (reducedFamily L S) v)).map
        (stabilizer (reducedFamily L S) v).subtype)) ∧
      Z (reducedFamily L S) v ≤ Z (reducedFamily L S) w :=
  reduced_normal_center_product h hvw hn
    (reduced_graph_core_obstruction h w v hvw.symm)

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
