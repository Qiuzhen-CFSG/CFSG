module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSpecialUnitaryEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveUnitaryEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.MixedLinearApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NonlinearSmallGraphApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EnlargementCatalogue

/-!
# Graph consumers with the remaining order-144 enlargement isolated

The actual enlarged quotient is now a marked rank-one model or has order
144. The latter alternative comes only from the unresolved strict PSU3(2)
enlargement. For endpoints excluding that concrete order, both adjacent-core
obstructions, source 6.6, and the literal Chapter 7 consumer follow for all
original families, including both degree-one unitary forms and mixed edges.

The order-144 alternative is retained; no ambient exclusion is asserted.
Full source assembly must still remove it and discharge the remaining
Chapter 6 duties. Source: DGS, Groups and Graphs (1985), 6.1, 6.5--6.6 and
7.1--7.5, pp.118--123 and 126--131; Aschbacher--Smith F.1.1 and F.1.9.
-/

open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Every original endpoint has a genuine enlarged rank-one marking or the
explicit remaining quotient order 144. No original family is discarded. -/
theorem reduced_enlargement_rankOne_or_order144 (h : HypothesisF11 L S) (i : Fin 2) :
    IsRankOneModel (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) ∨
      Nat.card (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) = 144 := by
  rcases reduced_enlargement_rankOne_or_small_unitary h i with hm | hp | hs
  · exact Or.inl hm
  · rcases original_small_projective_enlarged_marking_or_card h i hp with hp | hc
    · exact Or.inl (.projective_unitary 1 (by decide) (by simpa using hp))
    · exact Or.inr hc
  · exact Or.inl (.special_unitary 1 (by decide)
      (by simpa using original_small_special_enlarged_marking h i hs))

/-- The original parabolic-core consumer for PSU3(2), retaining only the
concrete order-144 enlargement as an outstanding alternative. -/
theorem original_small_projective_obstruction_of_no_order144 (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L (other i) ⧸ pCore 2 (L (other i))) 3 2)
    (hc : Nat.card (enlargedEndpoint L S (other i) ⧸ pCore 2 (enlargedEndpoint L S (other i))) ≠ 144) :
    (¬ enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) ∧
    (¬ parabolic L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))),
      (T : Subgroup (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i)))).map
        (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))).subtype =
          (parabolic L S i).pCoreIn 2 := by
  have he := (original_small_projective_enlarged_marking_or_card h (other i) hm).resolve_right hc
  exact original_small_unitary_enlargement_obstruction h i (Or.inl he)

/-- Both obstructions at the exact reduced endpoints, including both degree-one unitary forms. -/
theorem reduced_adjacent_core_obstruction_of_no_order144 (h : HypothesisF11 L S) (i : Fin 2)
    (hsmall : Nat.card (enlargedEndpoint L S (other i) ⧸ pCore 2 (enlargedEndpoint L S (other i))) ≠ 144) :
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
      rcases original_small_projective_enlarged_marking_or_card h (other i)
          (by simpa using hm) with hp | hc
      · exact reduced_small_unitary_enlargement_obstruction h i (Or.inl hp)
      · exact (hsmall hc).elim
    · exact reduced_nonlinear_adjacent_core_obstruction h i (Or.inr (Or.inl ⟨n,by omega,hm⟩))
  | special_unitary n hn hm =>
    by_cases he : n = 1
    · subst n
      exact reduced_small_unitary_enlargement_obstruction h i
        (Or.inr (original_small_special_enlarged_marking h (other i) (by simpa using hm)))
    · exact reduced_nonlinear_adjacent_core_obstruction h i (Or.inr (Or.inr (Or.inl ⟨n,by omega,hm⟩)))
  | dihedral hm => exact reduced_nonlinear_adjacent_core_obstruction h i (Or.inr (Or.inr (Or.inr hm)))

/-- The nonnormality clause of 6.5 at every edge, including both degree-one unitary forms. -/
theorem reduced_graph_core_obstruction_of_no_order144 (h : HypothesisF11 L S)
    (hsmall : ∀ i : Fin 2, Nat.card (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) ≠ 144)
    (v w : Vertex (reducedFamily L S)) (hvw : (graph (reducedFamily L S)).Adj v w) :
    ¬ stabilizer (reducedFamily L S) v ≤ normalizer
      ((Q (reducedFamily L S) w ⊓ Q (reducedFamily L S) v : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
  have hb (j : Bool) : ¬ stabilizer (reducedFamily L S) (base (reducedFamily L S) j) ≤ normalizer
      ((Q (reducedFamily L S) (base (reducedFamily L S) (!j)) ⊓
        Q (reducedFamily L S) (base (reducedFamily L S) j) : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
    intro hh
    simp only [Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hh
    cases j
    · exact (reduced_adjacent_core_obstruction_of_no_order144 h 1 (hsmall 0)).1
        ((localEnlargement_le _).trans hh)
    · exact (reduced_adjacent_core_obstruction_of_no_order144 h 0 (hsmall 1)).1
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
theorem reduced_graph_core_not_sylow_of_no_order144 (h : HypothesisF11 L S)
    (hsmall : ∀ i : Fin 2, Nat.card (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) ≠ 144)
    (v w : Vertex (reducedFamily L S)) (hvw : (graph (reducedFamily L S)).Adj v w) :
    ¬ ∃ T : Sylow 2 (conjugateSpanBy (Q (reducedFamily L S) w) (stabilizer (reducedFamily L S) v)),
      (T : Subgroup (conjugateSpanBy (Q (reducedFamily L S) w) (stabilizer (reducedFamily L S) v))).map
        (conjugateSpanBy (Q (reducedFamily L S) w) (stabilizer (reducedFamily L S) v)).subtype =
          Q (reducedFamily L S) w := by
  intro hs
  exact reduced_graph_core_obstruction_of_no_order144 h hsmall v w hvw
    (graph_core_inter_normal_of_sylow (reduced_triple h) hvw hs)

/-- The actual earlier-local interface, allowing mixed families and unequal endpoint fields. -/
@[expose] def reducedEarlierLocalTheoremsOfNoOrder144 (h : HypothesisF11 L S)
    (hsmall : ∀ i : Fin 2, Nat.card (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) ≠ 144) :
    CommutingNontrivial.EarlierLocalTheorems (reducedFamily L S) :=
  reducedEarlierLocalTheorems h (reduced_graph_core_obstruction_of_no_order144 h hsmall)

/-- Source 6.6 at every reduced edge, retaining the original graph and all actual Sylows. -/
theorem reduced_graph_center_product_of_no_order144 (h : HypothesisF11 L S)
    (hsmall : ∀ i : Fin 2, Nat.card (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) ≠ 144)
    {v w : Vertex (reducedFamily L S)} (hvw : (graph (reducedFamily L S)).Adj v w)
    (hn : stabilizer (reducedFamily L S) w ≤ normalizer
      (↑(Z (reducedFamily L S) v ⊔ Z (reducedFamily L S) w) : Set (G₀ L S))) :
    (∀ T : Sylow 2 (stabilizer (reducedFamily L S) v), Z (reducedFamily L S) v = omegaCenterIn
      ((T : Subgroup (stabilizer (reducedFamily L S) v)).map
        (stabilizer (reducedFamily L S) v).subtype)) ∧
      Z (reducedFamily L S) v ≤ Z (reducedFamily L S) w :=
  reduced_normal_center_product h hvw hn
    (reduced_graph_core_obstruction_of_no_order144 h hsmall w v hvw.symm)

/-- Every actual graph actor quotient has its original rank-one model away from the order-144 enlargement. -/
theorem reduced_actor_models_of_no_order144 (h : HypothesisF11 L S)
    (hsmall : ∀ i : Fin 2, Nat.card (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) ≠ 144)
    (v : Vertex (reducedFamily L S)) :
    IsRankOneModel (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)) := by
  have hi (i : Fin 2) : IsRankOneModel (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) :=
    (reduced_enlargement_rankOne_or_order144 h i).resolve_right (hsmall i)
  have hb (i : Bool) : IsRankOneModel (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) := by
    apply IsRankOneModel.of_equiv ?_ (reduced_graphEnlargementQuotient h i)
    cases i
    · exact hi 0
    · exact hi 1
  let F := reducedFamily L S
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  let A := graphLocalGroup F (base F v.type)
  have heq : A.map (MulAut.conj g).toMonoidHom = graphLocalGroup F v :=
    (graphLocalGroup_conjugate (reduced_triple h) g (base F v.type)).symm.trans
      (congrArg (graphLocalGroup F) hg)
  let a : A ≃* graphLocalGroup F v :=
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr heq)
  exact (hb v.type).of_equiv (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm

/-- The Chapter 7 consumer receives both actual actor models and the now-proved mixed-family obstruction.
The order-144 exclusion remains explicit for final source assembly. -/
theorem reduced_noncommuting_distance_bound_without_order144 (h : HypothesisF11 L S)
    (hsmall : ∀ i : Fin 2, Nat.card (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) ≠ 144)
    {v w : Vertex (reducedFamily L S)} (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥) :
    (b (reducedFamily L S) = 1 ∨ b (reducedFamily L S) = 2) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) v)
      (Z (reducedFamily L S) v) (Q (reducedFamily L S) v) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) w)
      (Z (reducedFamily L S) w) (Q (reducedFamily L S) w) :=
  Noncommuting.Reduction.reduced_distance_bound_of_actor_models h
    (reduced_actor_models_of_no_order144 h hsmall)
    (fun x y hxy => reduced_graph_core_obstruction_of_no_order144 h hsmall y x hxy.symm) hc hne
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
