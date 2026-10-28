module

public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs

/-!
# Normalized critical endpoints

A critical vertex is normalized so that the second base vertex lies on a
geodesic to it. The two endpoint modules then lie in the opposite edge
cores. Reversing at a neighbor whose seed moves the first ball produces
another normalized critical endpoint, using the same group element on
both endpoint labels.

Source: Aschbacher–Smith, F.9.10, F.9.13(2–4) and F.9.17,
combined manuscript (1 March 2004), printed pp.321–324.
-/

@[expose] public section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (stabilizer_base exists_smul_base incident_base)
open CFSG.Quasithin.ChapterF.Section07.Track
namespace CFSG.Quasithin.ChapterF.Section07.CriticalPairs
variable {G : Type*} [Group G] {F : Bool → Subgroup G}
variable (D : SourceSetup F) (hne : D.V ≠ ⊥)

/-- A representative of a critical endpoint normalized at the standard edge.
All conditions are propositions, so this family is finite when G is finite. -/
abbrev NormalizedEndpoint := {g : G //
  (graph F).dist (base F false) (g • base F true) = D.track hne ∧
  (graph F).dist (base F true) (g • base F true) + 1 = D.track hne ∧
  ¬ D.seed ≤ ballKernel F (g • base F true) 1}

namespace NormalizedEndpoint
variable {D hne}

abbrev vertex (i : NormalizedEndpoint D hne) : Vertex F := (i : G) • base F true

/-- F.9.10: local transitivity normalizes the first edge of a critical path. -/
theorem nonempty (hb : Odd (D.track hne)) : Nonempty (NormalizedEndpoint D hne) := by
  obtain ⟨v, hv, hc⟩ := (D.critical_witness hne).1
  have hvt := odd_endpoint_type F D hne hv hb
  have hne' : v ≠ base F false := by
    intro he
    rw [he, SimpleGraph.dist_self] at hv
    have := (D.track_spec hne).1
    omega
  obtain ⟨w, hw, hd⟩ := exists_predecessor F D.generates v (base F false) hne'
  obtain ⟨t, ht, htw⟩ := locally_transitive F
    (show (graph F).Adj (base F false) (base F true) from
      ⟨Bool.false_ne_true, incident_base F false true⟩) hw
  have htfix : t • base F false = base F false := ht
  have htinv : t⁻¹ • base F false = base F false := by
    calc
      t⁻¹ • base F false = t⁻¹ • (t • base F false) := congrArg (t⁻¹ • ·) htfix.symm
      _ = base F false := inv_smul_smul _ _
  have hnorm : D.seed.map (MulAut.conj t).toMonoidHom = D.seed :=
    mem_normalizer_iff_map_conj_eq.mp (D.seed_normalized (by
      simpa only [stabilizer_base] using ht))
  obtain ⟨g, hg⟩ := exists_smul_base F v
  rw [hvt] at hg
  refine ⟨⟨t⁻¹ * g, ?_, ?_, ?_⟩⟩
  · rw [mul_smul, hg, ← htinv, dist_smul F t⁻¹]
    exact hv
  · rw [mul_smul, hg, ← inv_smul_smul t (base F true), htw,
      dist_smul F t⁻¹, SimpleGraph.dist_comm]
    rw [hd]
    simpa only [SimpleGraph.dist_comm] using hv
  · intro h
    have hm := map_mono (f := (MulAut.conj t).toMonoidHom) h
    rw [hnorm, ← ballKernel_translate, mul_smul, hg, smul_inv_smul] at hm
    exact hc hm

variable (i : NormalizedEndpoint D hne)
include i

/-- Each seed fixes every endpoint at the critical distance. -/
theorem seed_le_stabilizer : D.seed ≤ stabilizer F i.vertex := by
  intro x hx
  exact (D.track_spec hne).2.1 hx i.vertex
    ((mem_ball_iff F D.generates _ _ _).mpr i.property.1.le)

/-- The adjacent edge at the base endpoint supplied by F.9.13(2). -/
theorem exists_base_edge (hb : 3 ≤ D.track hne) :
    ∃ w : Vertex F, w.type = false ∧ (graph F).Adj (base F true) w ∧
      vertexModule F D.seed i.vertex ≤
        (stabilizer F (base F true) ⊓ stabilizer F w).pCoreIn 2 := by
  have hd := i.property.2.1
  have hne' : i.vertex ≠ base F true := by
    intro he
    change (graph F).dist (base F true) i.vertex + 1 = _ at hd
    rw [he, SimpleGraph.dist_self] at hd
    omega
  obtain ⟨w, hw, hwd⟩ := exists_predecessor F D.generates i.vertex (base F true) hne'
  have hwt : w.type = false := by
    have hh := hw.1
    cases he : w.type <;> simp_all [base]
  refine ⟨w, hwt, hw, ?_⟩
  apply opposite_geodesic_edge_core F D hne (show i.vertex.type = true from rfl) _ hw
  have he : (graph F).dist i.vertex (base F true) + 1 = D.track hne := by
    simpa only [SimpleGraph.dist_comm] using hd
  omega

/-- The opposite edge supplies the reverse endpoint placement. -/
theorem exists_opposite_edge (hb : 3 ≤ D.track hne) :
    ∃ w : Vertex F, (graph F).Adj w i.vertex ∧
      vertexModule F D.seed (base F true) ≤
        (stabilizer F w ⊓ stabilizer F i.vertex).pCoreIn 2 := by
  have hd := i.property.2.1
  change (graph F).dist (base F true) i.vertex + 1 = _ at hd
  have hne' : base F true ≠ i.vertex := by
    intro he
    change (graph F).dist (base F true) i.vertex + 1 = _ at hd
    rw [← he, SimpleGraph.dist_self] at hd
    omega
  obtain ⟨w, hw, hwd⟩ := exists_predecessor F D.generates (base F true) i.vertex hne'
  refine ⟨w, hw.symm, ?_⟩
  exact geodesic_edge_core F D hne rfl (by omega) hw.symm

theorem endpoint_module_le (hb : 3 ≤ D.track hne) :
    vertexModule F D.seed i.vertex ≤ F true := by
  obtain ⟨w, _, _, hw⟩ := i.exists_base_edge hb
  exact (hw.trans ((pCoreIn_le 2 _).trans inf_le_left)).trans_eq
    (stabilizer_base F true)

theorem reverse_module_le (hb : 3 ≤ D.track hne) :
    vertexModule F D.seed (base F true) ≤ stabilizer F i.vertex := by
  obtain ⟨w, _, hw⟩ := i.exists_opposite_edge hb
  exact hw.trans ((pCoreIn_le 2 _).trans inf_le_right)

/-- F.9.13(3–4): the two endpoint modules normalize one another. -/
theorem commutator_le (hb : 3 ≤ D.track hne) :
    ⁅vertexModule F D.seed (base F true), vertexModule F D.seed i.vertex⁆ ≤
      vertexModule F D.seed (base F true) ⊓ vertexModule F D.seed i.vertex := by
  apply le_inf
  · apply le_normalizer_iff_commutator_le_left.mp
    exact (i.endpoint_module_le hb).trans (by
      simpa only [stabilizer_base] using
        stabilizer_normalizes_vertexModule F D.seed D.seed_normalized (base F true))
  · apply le_normalizer_iff_commutator_le_right.mp
    exact (i.reverse_module_le hb).trans
      (stabilizer_normalizes_vertexModule F D.seed D.seed_normalized i.vertex)

/-- A moving endpoint module has a moving seed among its neighbors. -/
theorem moving_neighbor
    (hm : ¬ vertexModule F D.seed i.vertex ≤ ballKernel F (base F true) 1) :
    ∃ w : Vertex F, (graph F).Adj i.vertex w ∧
      ¬ firstModule F D.seed w ≤ ballKernel F (base F true) 1 := by
  by_contra h
  apply hm
  rw [vertexModule_second F D.seed (show i.vertex.type = true from rfl)]
  apply iSup_le
  intro w
  apply iSup_le
  intro hw
  exact Classical.byContradiction (fun hn => h ⟨w, hw, hn⟩)

/-- F.9.17 before choosing any action coordinates: one conjugator carries
both endpoints to a new normalized pair. The second equation records that
its product with the old representative lies in the base stabilizer. -/
theorem reversal
    (hm : ¬ vertexModule F D.seed i.vertex ≤ ballKernel F (base F true) 1) :
    ∃ j : NormalizedEndpoint D hne, ((j : G) * (i : G)) ∈ F true := by
  obtain ⟨w, hw, hm⟩ := i.moving_neighbor hm
  have hwt : w.type = false := by
    have ht := hw.1
    cases he : w.type <;> simp_all [vertex, base]
  have hmin : D.track hne ≤ (graph F).dist w (base F true) :=
    critical_distance_minimal F D.generates
      (firstModule_le_ballKernel F D.seed D.seed_normalized (D.track_spec hne).2.1 hwt) hm
  have hdist : (graph F).dist w (base F true) = D.track hne := by
    have ht := (connected F D.generates).dist_triangle (u := w) (v := i.vertex)
      (w := base F true)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hw.symm] at ht
    have hd := i.property.2.1
    rw [SimpleGraph.dist_comm (u := base F true) (v := i.vertex)] at hd
    omega
  obtain ⟨k, hk₀, hk₁⟩ := incident_common_translate F hw.symm.2
  rw [hwt] at hk₀
  change k • base F true = i.vertex at hk₁
  have hcrit : ¬ D.seed ≤ ballKernel F (k⁻¹ • base F true) 1 := by
    intro hc
    apply hm
    have hc' := map_mono (f := (MulAut.conj k).toMonoidHom) hc
    rw [← firstModule_translate_base F D.seed D.seed_normalized,
      hk₀, ← ballKernel_translate, smul_inv_smul] at hc'
    exact hc'
  have hd₀ : (graph F).dist (base F false) (k⁻¹ • base F true) = D.track hne := by
    rw [← inv_smul_smul k (base F false), hk₀, dist_smul F k⁻¹]
    exact hdist
  have hd₁ : (graph F).dist (base F true) (k⁻¹ • base F true) + 1 = D.track hne := by
    calc
      _ = (graph F).dist (k⁻¹ • i.vertex) (k⁻¹ • base F true) + 1 := by
        rw [← hk₁, inv_smul_smul]
      _ = (graph F).dist i.vertex (base F true) + 1 := by rw [dist_smul F k⁻¹]
      _ = D.track hne := by simpa only [SimpleGraph.dist_comm] using i.property.2.1
  refine ⟨⟨k⁻¹, hd₀, hd₁, hcrit⟩, ?_⟩
  rw [← stabilizer_base F true]
  change (k⁻¹ * (i : G)) • base F true = base F true
  rw [mul_smul]
  change k⁻¹ • i.vertex = base F true
  rw [← hk₁, inv_smul_smul]

/-- An endpoint subgroup outside the vertex core moves the first ball.
Its edge-core containment is essential in this implication. -/
theorem moving_of_not_le_core (hb : 3 ≤ D.track hne) (U : Subgroup G)
    (hU : U ≤ vertexModule F D.seed i.vertex) (hn : ¬ U ≤ (F true).pCoreIn 2) :
    ¬ vertexModule F D.seed i.vertex ≤ ballKernel F (base F true) 1 := by
  intro hk
  apply hn
  obtain ⟨w, _, hw, hedge⟩ := i.exists_base_edge hb
  have hlocal : U ≤ (ballKernel F (base F true) 1).pCoreIn 2 :=
    (le_inf (hU.trans hk) (hU.trans hedge)).trans
      (Subgroup.inf_pCoreIn_le_of_le 2 (ballKernel_one_le_edge F hw))
  simpa only [stabilizer_base] using
    hlocal.trans (ballKernel_core_le_vertex_core F 2 (base F true) 1)

/-- Every H-invariant label is carried by the reversal's same conjugator. -/
theorem reversal_labels
    (hm : ¬ vertexModule F D.seed i.vertex ≤ ballKernel F (base F true) 1) :
    ∃ j : NormalizedEndpoint D hne,
      ∀ A : Subgroup G, F true ≤ normalizer (A : Set G) →
        (A.map (MulAut.conj (i : G)).toMonoidHom).map
          (MulAut.conj (j : G)).toMonoidHom = A := by
  obtain ⟨j, hj⟩ := i.reversal hm
  refine ⟨j, fun A hA => ?_⟩
  rw [map_map]
  have he : (MulAut.conj (j : G)).toMonoidHom.comp (MulAut.conj (i : G)).toMonoidHom =
      (MulAut.conj ((j : G) * (i : G))).toMonoidHom := by
    ext x
    simp [mul_assoc]
  rw [he]
  exact mem_normalizer_iff_map_conj_eq.mp (hA hj)

end NormalizedEndpoint
end CFSG.Quasithin.ChapterF.Section07.CriticalPairs
