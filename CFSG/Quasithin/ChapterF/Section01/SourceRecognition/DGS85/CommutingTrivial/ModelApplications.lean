module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.InitialRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AdjacentLinear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SuzukiEnlargement
public import Theory.Representation.RankOne.QuadraticRecognition.SourceTheorem

/-!
# Applying original linear model markings on the graph

When both original F.1.11 quotient rows are linear, the initial-recognition
transport supplies actual SL₂ markings at any two vertices of the corresponding
orbits.  The existing adjacent graph obstruction can then be applied literally,
including its original stabilizer and core.  Nonlinear source rows are not
classified here and remain explicit alternatives for the Chapter 9 assembly.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Representation.RankOne.QuadraticRecognition

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- A linear original model supplies an actual SL₂ marking at every vertex in
the matching graph orbit, together with its defining field data. -/
theorem reduced_vertex_linear_marking_of_original_model
    (h : HypothesisF11 L S) (v : Vertex (Reduction.reducedFamily L S))
    {n : ℕ}
    (hm : ClassicalGroup.IsPSL (family L v.type ⧸ pCore 2 (family L v.type)) 2 (2 ^ n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      0 < n ∧ Nat.card F = 2 ^ n ∧
      Nonempty ((graphLocalGroup (Reduction.reducedFamily L S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) v)) ≃* SL(2, F)) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hpos : 1 < Nat.card F := Finite.one_lt_card
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    rw [hcard] at hpos
    norm_num at hpos
  exact ⟨F, hF, hfin, inferInstance, hn, hcard,
    reduced_vertex_linear_marking h v e⟩

/- A graph quotient model, rather than merely a marking, is useful to the
source catalogue dispatcher.  The construction keeps the defining field and
the actual quotient carrier; it does not identify a graph marking with an
original endpoint by fiat. -/
theorem reduced_vertex_binary_model_of_original_linear
    {G : Type} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (v : Vertex (Reduction.reducedFamily L S))
    {n : ℕ}
    (hm : ClassicalGroup.IsPSL (family L v.type ⧸ pCore 2 (family L v.type)) 2 (2 ^ n)) :
    Nonempty (BinaryRankOneModel
      (graphLocalGroup (Reduction.reducedFamily L S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) v))) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hpos : 1 < Nat.card F := Finite.one_lt_card
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    rw [hcard] at hpos
    norm_num at hpos
  obtain ⟨eGraph⟩ := reduced_vertex_linear_marking h v e
  exact ⟨.sl2 F n hn hcard eGraph⟩

theorem reduced_vertex_binary_model_of_original_suzuki
    {G : Type} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (v : Vertex (Reduction.reducedFamily L S))
    {m : ℕ} (hm : 0 < m)
    (e : (family L v.type ⧸ pCore 2 (family L v.type)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    Nonempty (BinaryRankOneModel
      (graphLocalGroup (Reduction.reducedFamily L S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) v))) := by
  let F₀ := Reduction.reducedFamily L S
  let e₀ := Classical.choice
    (show Nonempty ((graphLocalGroup F₀ (base F₀ v.type) ⧸
      pCore 2 (graphLocalGroup F₀ (base F₀ v.type))) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) from
      ⟨Reduction.reduced_graphSuzukiQuotient h v.type hm e⟩)
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base F₀ v
  let A := graphLocalGroup F₀ (base F₀ v.type)
  have heq : A.map (MulAut.conj g).toMonoidHom = graphLocalGroup F₀ v := by
    rw [← hg]
    exact (graphLocalGroup_conjugate (Reduction.reduced_triple h) g
      (Subgroup.CosetGeometry.base F₀ v.type)).symm
  let a : A ≃* graphLocalGroup F₀ v :=
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr heq)
  let f := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm
  exact ⟨.suzuki m (f.trans e₀)⟩

/- The original linear rows give markings at any two actual graph vertices,
with their fields and source cardinality parameters retained. -/
theorem reduced_original_linear_vertex_markings
    (h : HypothesisF11 L S)
    (hm : ∀ i : Bool, ∃ n : ℕ,
      0 < n ∧ ClassicalGroup.IsPSL
        (family L i ⧸ pCore 2 (family L i)) 2 (2 ^ n))
    (v w : Vertex (Reduction.reducedFamily L S)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (n m : ℕ),
      0 < n ∧ Nat.card F = 2 ^ n ∧
      0 < m ∧ Nat.card K = 2 ^ m ∧
      Nonempty ((graphLocalGroup (Reduction.reducedFamily L S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) v)) ≃* SL(2, F)) ∧
      Nonempty ((graphLocalGroup (Reduction.reducedFamily L S) w ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) w)) ≃* SL(2, K)) := by
  obtain ⟨n, hn, hnv⟩ := hm v.type
  obtain ⟨m, hmpos, hmw⟩ := hm w.type
  obtain ⟨F, hF, hFfin, hFchar, hnpos, hFcard, ⟨ev⟩⟩ :=
    reduced_vertex_linear_marking_of_original_model h v hnv
  obtain ⟨K, hK, hKfin, hKchar, hmpos', hKcard, ⟨ew⟩⟩ :=
    reduced_vertex_linear_marking_of_original_model h w hmw
  exact ⟨F, hF, hFfin, hFchar, K, hK, hKfin, hKchar, n, m,
    hnpos, hFcard, hmpos', hKcard, ⟨ev⟩, ⟨ew⟩⟩

/-- If both original quotient rows are linear, source 6.5 holds at every
edge, with the supplied two graph endpoints and full stabilizer. -/
theorem adjacent_linear_graph_core_obstruction_of_original_models
    (h : HypothesisF11 L S)
    {a beta : Vertex (Reduction.reducedFamily L S)}
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hm : ∀ i : Bool, ∃ n : ℕ,
      0 < n ∧ ClassicalGroup.IsPSL
        (family L i ⧸ pCore 2 (family L i)) 2 (2 ^ n))
    (v w : Vertex (Reduction.reducedFamily L S))
    (hvw : (graph (Reduction.reducedFamily L S)).Adj v w) :
    ¬ stabilizer (Reduction.reducedFamily L S) v ≤ normalizer
      ((Q (Reduction.reducedFamily L S) w ⊓ Q (Reduction.reducedFamily L S) v :
        Subgroup (Reduction.G₀ L S)) : Set (Reduction.G₀ L S)) := by
  obtain ⟨n, hn, hmα⟩ := hm a.type
  obtain ⟨m, hmpos, hmβ⟩ := hm beta.type
  obtain ⟨F, hF, hFfin, hFchar, _, _, ⟨eα⟩⟩ :=
    reduced_vertex_linear_marking_of_original_model h a hmα
  obtain ⟨K, hK, hKfin, hKchar, _, _, ⟨eβ⟩⟩ :=
    reduced_vertex_linear_marking_of_original_model h beta hmβ
  exact adjacent_linear_graph_core_obstruction (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hab eα eβ v w hvw

/- The same original linear hypotheses discharge the full 6.5 obstruction on
every adjacent pair of the actual reduced graph. -/
theorem reduced_original_linear_graph_core_obstruction
    (h : HypothesisF11 L S)
    (hm : ∀ i : Bool, ∃ n : ℕ,
      0 < n ∧ ClassicalGroup.IsPSL
        (family L i ⧸ pCore 2 (family L i)) 2 (2 ^ n))
    {v w : Vertex (Reduction.reducedFamily L S)}
    (hvw : (graph (Reduction.reducedFamily L S)).Adj v w) :
    ¬ stabilizer (Reduction.reducedFamily L S) v ≤ normalizer
      ((Q (Reduction.reducedFamily L S) w ⊓ Q (Reduction.reducedFamily L S) v :
        Subgroup (Reduction.G₀ L S)) : Set (Reduction.G₀ L S)) := by
  exact adjacent_linear_graph_core_obstruction_of_original_models h hvw hm v w hvw

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
