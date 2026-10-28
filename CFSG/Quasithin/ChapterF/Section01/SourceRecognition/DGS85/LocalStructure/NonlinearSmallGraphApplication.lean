module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSolvableApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.ActorData

/-!
# Nonlinear local conclusions with the small solvable rows included

The original quotient catalogue here includes every Suzuki parameter,
D₁₀, and both unitary forms of degree at least two. The small solvable
replacement proof and the large nonlinear proofs give both 6.5 clauses
at every reduced edge. The actual enlarged models, earlier-local interface
and 6.6 center control then feed the original Chapter 7 consumer.

Endpoint fields and families may differ, and cubic scalar centers and the
strict D₁₀-to-Sz(2) enlargement are retained. The degree-one unitary forms
and mixed linear/nonlinear orientations remain separate source obligations.
Source: DGS, Groups and Graphs (1985), 6.1, 6.5--6.6, pp.118--123,
and 7.1--7.5, pp.126--131.
-/

open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Actual nonlinear source models, retaining all Suzuki parameters and D10.
The two degree-one unitary forms remain outside this proved branch. -/
@[expose] def NonlinearLocalModel (H : Type*) [Group H] : Prop :=
  (∃ m : ℕ, Nonempty (H ≃* SuzukiMatrixGroup m)) ∨
  (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU H 3 (2^n)) ∨
  (∃ n : ℕ, 2 ≤ n ∧ IsSU H 3 (2^n)) ∨ Nonempty (H ≃* DihedralGroup 5)

/-- Both 6.5 obstructions for every Suzuki or dihedral endpoint and every unitary endpoint of degree at least two. -/
theorem reduced_nonlinear_adjacent_core_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    (hmodel : NonlinearLocalModel (L (other i) ⧸ pCore 2 (L (other i)))) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    (¬ localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set (G₀ L S))) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 := by
  rcases hmodel with hsz | hm | hm | hd
  · obtain ⟨m,⟨e⟩⟩ := hsz
    cases m with
    | zero => exact reduced_small_solvable_adjacent_core_obstruction h i (Or.inr ⟨e⟩)
    | succ m => exact reduced_suzuki_adjacent_core_obstruction h i (Nat.succ_pos m) e
  · exact reduced_large_nonlinear_adjacent_core_obstruction h i (Or.inr (Or.inl hm))
  · exact reduced_large_nonlinear_adjacent_core_obstruction h i (Or.inr (Or.inr hm))
  · exact reduced_small_solvable_adjacent_core_obstruction h i (Or.inl hd)

/-- The original nonlinear markings give the actual 6.5 obstruction at every edge of the reduced graph. -/
theorem reduced_nonlinear_graph_core_obstruction (h : HypothesisF11 L S)
    (hmodel : ∀ i : Fin 2,
      NonlinearLocalModel (L i ⧸ pCore 2 (L i)))
    (v w : Vertex (reducedFamily L S)) (hvw : (graph (reducedFamily L S)).Adj v w) :
    ¬ stabilizer (reducedFamily L S) v ≤ normalizer
      ((Q (reducedFamily L S) w ⊓ Q (reducedFamily L S) v : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
  have hb (j : Bool) : ¬ stabilizer (reducedFamily L S) (base (reducedFamily L S) j) ≤ normalizer
      ((Q (reducedFamily L S) (base (reducedFamily L S) (!j)) ⊓
        Q (reducedFamily L S) (base (reducedFamily L S) j) : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
    intro hh
    simp only [Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hh
    cases j
    · exact (reduced_nonlinear_adjacent_core_obstruction h 1 (hmodel 0)).1
        ((localEnlargement_le _).trans hh)
    · exact (reduced_nonlinear_adjacent_core_obstruction h 0 (hmodel 1)).1
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
theorem reduced_nonlinear_graph_core_not_sylow (h : HypothesisF11 L S)
    (hmodel : ∀ i : Fin 2, NonlinearLocalModel (L i ⧸ pCore 2 (L i)))
    (v w : Vertex (reducedFamily L S)) (hvw : (graph (reducedFamily L S)).Adj v w) :
    ¬ ∃ T : Sylow 2 (conjugateSpanBy (Q (reducedFamily L S) w) (stabilizer (reducedFamily L S) v)),
      (T : Subgroup (conjugateSpanBy (Q (reducedFamily L S) w) (stabilizer (reducedFamily L S) v))).map
        (conjugateSpanBy (Q (reducedFamily L S) w) (stabilizer (reducedFamily L S) v)).subtype =
          Q (reducedFamily L S) w := by
  intro hs
  exact reduced_nonlinear_graph_core_obstruction h hmodel v w hvw
    (graph_core_inter_normal_of_sylow (reduced_triple h) hvw hs)

/-- The complete earlier-local interface on the nonlinear reduced graph, with its 6.5 premise discharged. -/
@[expose] def reducedNonlinearEarlierLocalTheorems (h : HypothesisF11 L S)
    (hmodel : ∀ i : Fin 2,
      NonlinearLocalModel (L i ⧸ pCore 2 (L i))) :
    CommutingNontrivial.EarlierLocalTheorems (reducedFamily L S) :=
  reducedEarlierLocalTheorems h (reduced_nonlinear_graph_core_obstruction h hmodel)

/-- Source 6.6 at every reduced edge, retaining the original graph and all actual Sylows. -/
theorem reduced_nonlinear_graph_normal_center_product (h : HypothesisF11 L S)
    (hmodel : ∀ i : Fin 2,
      NonlinearLocalModel (L i ⧸ pCore 2 (L i)))
    {v w : Vertex (reducedFamily L S)} (hvw : (graph (reducedFamily L S)).Adj v w)
    (hn : stabilizer (reducedFamily L S) w ≤ normalizer
      (↑(Z (reducedFamily L S) v ⊔ Z (reducedFamily L S) w) : Set (G₀ L S))) :
    (∀ T : Sylow 2 (stabilizer (reducedFamily L S) v), Z (reducedFamily L S) v = omegaCenterIn
      ((T : Subgroup (stabilizer (reducedFamily L S) v)).map
        (stabilizer (reducedFamily L S) v).subtype)) ∧
      Z (reducedFamily L S) v ≤ Z (reducedFamily L S) w :=
  reduced_normal_center_product h hvw hn
    (reduced_nonlinear_graph_core_obstruction h hmodel w v hvw.symm)

/-- Each actual graph actor has its marked source model, with both original quotient forms retained. -/
theorem reduced_nonlinear_actor_models (h : HypothesisF11 L S)
    (hmodel : ∀ i : Fin 2,
      NonlinearLocalModel (L i ⧸ pCore 2 (L i)))
    (v : Vertex (reducedFamily L S)) :
    IsRankOneModel (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)) := by
  have hb (j : Bool) : IsRankOneModel (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) j) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) j))) := by
    have hm : NonlinearLocalModel (family L j ⧸ pCore 2 (family L j)) := by
      cases j
      · exact hmodel 0
      · exact hmodel 1
    rcases hm with hsz | hp | hs | hd
    · obtain ⟨m,⟨e⟩⟩ := hsz
      exact .suzuki m ⟨reduced_graphSuzukiQuotient_all h j m e⟩
    · obtain ⟨n,hn,hm⟩ := hp
      obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
      let := hF
      let := hfin
      exact .projective_unitary n (by omega) ⟨F,hF,hfin,J,hcard,hconj,
        ⟨reduced_graphProjectiveUnitaryQuotient h j J hn hcard hconj e⟩⟩
    · obtain ⟨n,hn,hm⟩ := hs
      obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
      let := hF
      let := hfin
      exact .special_unitary n (by omega) ⟨F,hF,hfin,J,hcard,hconj,
        ⟨reduced_graphSpecialUnitaryQuotient h j J hn hcard hconj e⟩⟩
    · obtain ⟨e⟩ := hd
      exact reduced_graph_dihedral_rankOne h j e
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

/-- The actual Chapter 7 application discharges both model and obstruction premises on this source branch. -/
theorem reduced_nonlinear_noncommuting_distance_bound (h : HypothesisF11 L S)
    (hmodel : ∀ i : Fin 2,
      NonlinearLocalModel (L i ⧸ pCore 2 (L i)))
    {v w : Vertex (reducedFamily L S)} (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥) :
    (b (reducedFamily L S) = 1 ∨ b (reducedFamily L S) = 2) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) v)
      (Z (reducedFamily L S) v) (Q (reducedFamily L S) v) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) w)
      (Z (reducedFamily L S) w) (Q (reducedFamily L S) w) :=
  Noncommuting.Reduction.reduced_distance_bound_of_actor_models h
    (reduced_nonlinear_actor_models h hmodel)
    (fun x y hxy => reduced_nonlinear_graph_core_obstruction h hmodel y x hxy.symm) hc hne
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
