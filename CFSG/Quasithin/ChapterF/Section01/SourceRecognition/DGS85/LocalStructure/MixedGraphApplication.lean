module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.MixedLinearApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NonlinearSmallGraphApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EnlargementCatalogue

/-!
# Mixed-family graph assembly with only small-unitary cases outstanding

The opposite endpoint in the linear obstruction now uses its actual
original rank-one model. Splitting each original quotient independently
therefore covers all mixed orientations as well as both homogeneous branches.
The resulting 6.5 and 6.6 conclusions construct the actual earlier-local
interface and discharge the obstruction in the Chapter 7 application.

The only extra assumption here excludes the two original degree-one
unitary rows. It remains a source obligation; neither solvability nor the
build of this conditional assembly proves that exclusion.
Source: DGS, Groups and Graphs (1985), 6.5--6.6, pp.121--123,
and the earlier-local inputs to Chapters 7--9.
-/

open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Only the neighboring degree-one unitary rows remain in the general original endpoint split. -/
theorem reduced_adjacent_core_obstruction_of_no_small_unitary (h : HypothesisF11 L S) (i : Fin 2)
    (hsmall : ¬ ClassicalGroup.IsPSU (L (other i) ⧸ pCore 2 (L (other i))) 3 2 ∧
      ¬ IsSU (L (other i) ⧸ pCore 2 (L (other i))) 3 2) :
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
      exact (hsmall.1 (by simpa using hm)).elim
    · exact reduced_nonlinear_adjacent_core_obstruction h i (Or.inr (Or.inl ⟨n,by omega,hm⟩))
  | special_unitary n hn hm =>
    by_cases he : n = 1
    · subst n
      exact (hsmall.2 (by simpa using hm)).elim
    · exact reduced_nonlinear_adjacent_core_obstruction h i (Or.inr (Or.inr (Or.inl ⟨n,by omega,hm⟩)))
  | dihedral hm => exact reduced_nonlinear_adjacent_core_obstruction h i (Or.inr (Or.inr (Or.inr hm)))

/-- Both mixed orientations and all previous branches give 6.5 at every edge, away from the small-unitary rows. -/
theorem reduced_graph_core_obstruction_of_no_small_unitary (h : HypothesisF11 L S)
    (hsmall : ∀ i : Fin 2, ¬ ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2 ∧
      ¬ IsSU (L i ⧸ pCore 2 (L i)) 3 2)
    (v w : Vertex (reducedFamily L S)) (hvw : (graph (reducedFamily L S)).Adj v w) :
    ¬ stabilizer (reducedFamily L S) v ≤ normalizer
      ((Q (reducedFamily L S) w ⊓ Q (reducedFamily L S) v : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
  have hb (j : Bool) : ¬ stabilizer (reducedFamily L S) (base (reducedFamily L S) j) ≤ normalizer
      ((Q (reducedFamily L S) (base (reducedFamily L S) (!j)) ⊓
        Q (reducedFamily L S) (base (reducedFamily L S) j) : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
    intro hh
    simp only [Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hh
    cases j
    · exact (reduced_adjacent_core_obstruction_of_no_small_unitary h 1 (hsmall 0)).1
        ((localEnlargement_le _).trans hh)
    · exact (reduced_adjacent_core_obstruction_of_no_small_unitary h 0 (hsmall 1)).1
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
theorem reduced_graph_core_not_sylow_of_no_small_unitary (h : HypothesisF11 L S)
    (hsmall : ∀ i : Fin 2, ¬ ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2 ∧
      ¬ IsSU (L i ⧸ pCore 2 (L i)) 3 2)
    (v w : Vertex (reducedFamily L S)) (hvw : (graph (reducedFamily L S)).Adj v w) :
    ¬ ∃ T : Sylow 2 (conjugateSpanBy (Q (reducedFamily L S) w) (stabilizer (reducedFamily L S) v)),
      (T : Subgroup (conjugateSpanBy (Q (reducedFamily L S) w) (stabilizer (reducedFamily L S) v))).map
        (conjugateSpanBy (Q (reducedFamily L S) w) (stabilizer (reducedFamily L S) v)).subtype =
          Q (reducedFamily L S) w := by
  intro hs
  exact reduced_graph_core_obstruction_of_no_small_unitary h hsmall v w hvw
    (graph_core_inter_normal_of_sylow (reduced_triple h) hvw hs)

/-- The actual earlier-local interface, allowing mixed families and unequal endpoint fields. -/
@[expose] def reducedEarlierLocalTheoremsOfNoSmallUnitary (h : HypothesisF11 L S)
    (hsmall : ∀ i : Fin 2, ¬ ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2 ∧
      ¬ IsSU (L i ⧸ pCore 2 (L i)) 3 2) :
    CommutingNontrivial.EarlierLocalTheorems (reducedFamily L S) :=
  reducedEarlierLocalTheorems h (reduced_graph_core_obstruction_of_no_small_unitary h hsmall)

/-- Source 6.6 at every reduced edge, retaining the original graph and all actual Sylows. -/
theorem reduced_graph_center_product_of_no_small_unitary (h : HypothesisF11 L S)
    (hsmall : ∀ i : Fin 2, ¬ ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2 ∧
      ¬ IsSU (L i ⧸ pCore 2 (L i)) 3 2)
    {v w : Vertex (reducedFamily L S)} (hvw : (graph (reducedFamily L S)).Adj v w)
    (hn : stabilizer (reducedFamily L S) w ≤ normalizer
      (↑(Z (reducedFamily L S) v ⊔ Z (reducedFamily L S) w) : Set (G₀ L S))) :
    (∀ T : Sylow 2 (stabilizer (reducedFamily L S) v), Z (reducedFamily L S) v = omegaCenterIn
      ((T : Subgroup (stabilizer (reducedFamily L S) v)).map
        (stabilizer (reducedFamily L S) v).subtype)) ∧
      Z (reducedFamily L S) v ≤ Z (reducedFamily L S) w :=
  reduced_normal_center_product h hvw hn
    (reduced_graph_core_obstruction_of_no_small_unitary h hsmall w v hvw.symm)

/-- The Chapter 7 consumer receives both actual actor models and the now-proved mixed-family obstruction.
The two small-unitary exclusions remain explicit for final source assembly. -/
theorem reduced_noncommuting_distance_bound_without_small_unitary (h : HypothesisF11 L S)
    (hsmall : ∀ i : Fin 2, ¬ ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2 ∧
      ¬ IsSU (L i ⧸ pCore 2 (L i)) 3 2)
    {v w : Vertex (reducedFamily L S)} (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥) :
    (b (reducedFamily L S) = 1 ∨ b (reducedFamily L S) = 2) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) v)
      (Z (reducedFamily L S) v) (Q (reducedFamily L S) v) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) w)
      (Z (reducedFamily L S) w) (Q (reducedFamily L S) w) :=
  reduced_noncommuting_distance_bound_of_no_small_unitary h hsmall
    (fun x y hxy => reduced_graph_core_obstruction_of_no_small_unitary h hsmall y x hxy.symm) hc hne
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
