module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NonlinearObstructionApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.ActorData

/-!
# Large nonlinear local conclusions on every reduced edge

The original Suzuki and unitary markings give actual enlarged-quotient
models in both vertex orbits. Common-edge conjugation transports the
proved adjacent-core obstruction to every edge, constructing the earlier
local interface and the 6.6 conclusion. The Chapter 7 consumer receives
both its model and obstruction premises from these original markings.

The fields and nonlinear families at the endpoints may differ. Small
rows and mixed linear/nonlinear orientations remain outside this theorem.
Source: DGS, Groups and Graphs (1985), 6.5--6.6, pp.121--123 and
7.1--7.5, pp.126--131.
-/

open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original large nonlinear markings give the actual 6.5 obstruction at every edge of the reduced graph. -/
theorem reduced_large_nonlinear_graph_core_obstruction (h : HypothesisF11 L S)
    (hmodel : ∀ i : Fin 2,
      (∃ m : ℕ, 0 < m ∧ Nonempty ((L i ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 (2^n)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ IsSU (L i ⧸ pCore 2 (L i)) 3 (2^n)))
    (v w : Vertex (reducedFamily L S)) (hvw : (graph (reducedFamily L S)).Adj v w) :
    ¬ stabilizer (reducedFamily L S) v ≤ normalizer
      ((Q (reducedFamily L S) w ⊓ Q (reducedFamily L S) v : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
  have hb (j : Bool) : ¬ stabilizer (reducedFamily L S) (base (reducedFamily L S) j) ≤ normalizer
      ((Q (reducedFamily L S) (base (reducedFamily L S) (!j)) ⊓
        Q (reducedFamily L S) (base (reducedFamily L S) j) : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
    intro hh
    simp only [Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hh
    cases j
    · exact (reduced_large_nonlinear_adjacent_core_obstruction h 1 (hmodel 0)).1
        ((localEnlargement_le _).trans hh)
    · exact (reduced_large_nonlinear_adjacent_core_obstruction h 0 (hmodel 1)).1
        ((localEnlargement_le _).trans hh)
  obtain ⟨g,hv,hw⟩ := incident_common_translate (reducedFamily L S) hvw.2
  have ht : w.type = !v.type := Bool.eq_not_of_ne hvw.1.symm
  intro hh
  rw [←hv,←hw,Q_translate,Q_translate,stabilizer_translate,
    ←Subgroup.map_inf _ _ _ (MulAut.conj g).injective,←map_equiv_normalizer_eq] at hh
  have hh' := (map_le_map_iff_of_injective (MulAut.conj g).injective).mp hh
  rw [ht] at hh'
  exact hb v.type hh'

/-- The complete earlier-local interface on the large nonlinear reduced graph, with its 6.5 premise discharged. -/
@[expose] def reducedLargeNonlinearEarlierLocalTheorems (h : HypothesisF11 L S)
    (hmodel : ∀ i : Fin 2,
      (∃ m : ℕ, 0 < m ∧ Nonempty ((L i ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 (2^n)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ IsSU (L i ⧸ pCore 2 (L i)) 3 (2^n))) :
    CommutingNontrivial.EarlierLocalTheorems (reducedFamily L S) :=
  reducedEarlierLocalTheorems h (reduced_large_nonlinear_graph_core_obstruction h hmodel)

/-- Source 6.6 at every reduced edge, retaining the original graph and all actual Sylows. -/
theorem reduced_large_nonlinear_graph_normal_center_product (h : HypothesisF11 L S)
    (hmodel : ∀ i : Fin 2,
      (∃ m : ℕ, 0 < m ∧ Nonempty ((L i ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 (2^n)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ IsSU (L i ⧸ pCore 2 (L i)) 3 (2^n)))
    {v w : Vertex (reducedFamily L S)} (hvw : (graph (reducedFamily L S)).Adj v w)
    (hn : stabilizer (reducedFamily L S) w ≤ normalizer
      (↑(Z (reducedFamily L S) v ⊔ Z (reducedFamily L S) w) : Set (G₀ L S))) :
    (∀ T : Sylow 2 (stabilizer (reducedFamily L S) v), Z (reducedFamily L S) v = omegaCenterIn
      ((T : Subgroup (stabilizer (reducedFamily L S) v)).map
        (stabilizer (reducedFamily L S) v).subtype)) ∧
      Z (reducedFamily L S) v ≤ Z (reducedFamily L S) w :=
  reduced_normal_center_product h hvw hn
    (reduced_large_nonlinear_graph_core_obstruction h hmodel w v hvw.symm)

/-- Each actual graph actor has its marked source model, with both original quotient forms retained. -/
theorem reduced_large_nonlinear_actor_models (h : HypothesisF11 L S)
    (hmodel : ∀ i : Fin 2,
      (∃ m : ℕ, 0 < m ∧ Nonempty ((L i ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 (2^n)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ IsSU (L i ⧸ pCore 2 (L i)) 3 (2^n)))
    (v : Vertex (reducedFamily L S)) :
    IsRankOneModel (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)) := by
  have hb (j : Bool) : IsRankOneModel (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) j) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) j))) := by
    have hm : (∃ m : ℕ, 0 < m ∧ Nonempty ((family L j ⧸ pCore 2 (family L j)) ≃*
        SuzukiMatrixGroup m)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU (family L j ⧸ pCore 2 (family L j)) 3 (2^n)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ IsSU (family L j ⧸ pCore 2 (family L j)) 3 (2^n)) := by
      cases j
      · exact hmodel 0
      · exact hmodel 1
    rcases hm with ⟨m,hm,⟨e⟩⟩ | ⟨n,hn,hm⟩ | ⟨n,hn,hm⟩
    · exact .suzuki m ⟨reduced_graphSuzukiQuotient h j hm e⟩
    · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
      let := hF
      let := hfin
      exact .projective_unitary n (by omega) ⟨F,hF,hfin,J,hcard,hconj,
        ⟨reduced_graphProjectiveUnitaryQuotient h j J hn hcard hconj e⟩⟩
    · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
      let := hF
      let := hfin
      exact .special_unitary n (by omega) ⟨F,hF,hfin,J,hcard,hconj,
        ⟨reduced_graphSpecialUnitaryQuotient h j J hn hcard hconj e⟩⟩
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
theorem reduced_large_nonlinear_noncommuting_distance_bound (h : HypothesisF11 L S)
    (hmodel : ∀ i : Fin 2,
      (∃ m : ℕ, 0 < m ∧ Nonempty ((L i ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 (2^n)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ IsSU (L i ⧸ pCore 2 (L i)) 3 (2^n)))
    {v w : Vertex (reducedFamily L S)} (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥) :
    (b (reducedFamily L S) = 1 ∨ b (reducedFamily L S) = 2) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) v)
      (Z (reducedFamily L S) v) (Q (reducedFamily L S) v) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) w)
      (Z (reducedFamily L S) w) (Q (reducedFamily L S) w) :=
  Noncommuting.Reduction.reduced_distance_bound_of_actor_models h
    (reduced_large_nonlinear_actor_models h hmodel)
    (fun x y hxy => reduced_large_nonlinear_graph_core_obstruction h hmodel y x hxy.symm) hc hne
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
