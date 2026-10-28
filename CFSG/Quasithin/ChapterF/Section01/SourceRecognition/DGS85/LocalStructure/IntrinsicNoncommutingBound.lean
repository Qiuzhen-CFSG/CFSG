module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicTerminalGeometry

/-!
# The original noncommuting distance bound without a global actor catalogue

In a hypothetical branch with b > 4, the intrinsic radius/core calculations
construct the actual terminal linear quotient. The terminal vertex is on
the opposite orbit from the critical endpoint, so these two markings now
supply the global actor catalogue required by the existing Chapter 7 distance
implication. Applying that proved implication closes the long branch.
The intrinsic forward identities and distinct-neighbor theorem exclude b=4;
the already proved parity and positivity finish the original b=1 or b=2 bound.

This is a source-specialized discharge of the missing actor-model premise,
not a proof of the unrestricted enlargement catalogue. In particular the
possible order-144 enlargement outside this noncommuting argument and the
remaining general source assembly are retained. The original full Borel,
reduced inclusions, cores and potentially infinite completion are unchanged.
Source: DGS, *Groups and Graphs* (1985), Theorem B(a), p.102, and
(7.4)--(7.5), pp.128--131. The long-distance implication is reused from
`Noncommuting.SourceConclusion`; its Chapter 7 proof is not duplicated.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Noncommuting
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- Construct an opposite-orbit terminal quotient from the original long-branch geometry. -/
theorem reduced_long_terminal_model_exists (h : HypothesisF11 L S)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 4 < b F) :
    ∃ t : Vertex F, v.type ≠ t.type ∧ ∃ n, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup F t ⧸ pCore 2 (graphLocalGroup F t)) 2 (2^n) := by
  let ht := reduced_triple h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have heven := reduced_long_critical_even h hc hne (by omega)
  have hbl : 6 ≤ b F := by obtain ⟨n,hn⟩ := heven.2; omega
  have hvw : v ≠ w := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self] at hh
    omega
  obtain ⟨t,hwt,hdt⟩ := exists_predecessor F ht.generate v w hvw
  rw [hc.1] at hdt
  have hvt : v ≠ t := by intro he; rw [he,SimpleGraph.dist_self] at hdt; omega
  obtain ⟨y,hty,hdy⟩ := exists_predecessor F ht.generate v t hvt
  have hvy : v ≠ y := by
    intro he
    subst y
    simp only [SimpleGraph.dist_self] at hdy
    omega
  obtain ⟨x,hyx,hdx⟩ := exists_predecessor F ht.generate v y hvy
  have hcore := reduced_long_terminal_core_containment h hc hne (by omega) hwt hty hyx hdt hdy hdx
  have hsyl := (reduced_critical_natural_centers_and_products h hc hne).2.2.2.1
  have hesc₀ := graph_radius_two_escape_of_maximal_edges ht (reduced_kernel_sylow h) hc hne
    (by omega) hsyl (fun _ he => graph_edge_isCoatom ht he)
  have hesc : ¬ V F v 2 ≤ Q F t := by
    intro hh
    exact hesc₀ ((hh.trans (source_Z_Q_U ht t).2).trans
      ((ballKernel_one_le_edge F hwt.symm).trans inf_le_right))
  obtain ⟨u,a,x',hvu,hva,hua,hyx',hdu,hdx',ha⟩ :=
    graph_terminal_actor_configuration ht (reduced_kernel_sylow h) hc hbl hwt hty (by omega) hesc
  have hmodel := reduced_long_terminal_linear h hc hne hb hvu hwt hva hua hdu hdt hty hyx'
    hdx' hcore ha
  refine ⟨t,?_,hmodel⟩
  have hw := (same_orbit_iff F v w).mp heven.1
  exact fun hh => hwt.1 (hw.symm.trans hh)

/-- Critical and terminal markings cover both vertex orbits in the contrary long branch. -/
theorem reduced_long_actor_models (h : HypothesisF11 L S)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 4 < b F) (x : Vertex F) :
    IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)) := by
  obtain ⟨t,hvt,nt,hnt,hmt⟩ := reduced_long_terminal_model_exists h hc hne hb
  obtain ⟨nv,hnv,hmv⟩ := (reduced_critical_actor_quotients_linear h hc hne).1
  have transport (a : Vertex F) (ha : a.type = x.type)
      (hm : IsRankOneModel (graphLocalGroup F a ⧸ pCore 2 (graphLocalGroup F a))) :
      IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)) := by
    obtain ⟨g,hg⟩ := (same_orbit_iff F a x).mpr ha
    let A := graphLocalGroup F a
    have he : A.map (MulAut.conj g).toMonoidHom = graphLocalGroup F x :=
      (graphLocalGroup_conjugate (reduced_triple h) g a).symm.trans
        (congrArg (graphLocalGroup F) hg)
    let e : A ≃* graphLocalGroup F x :=
      (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
        (MulEquiv.subgroupCongr he)
    exact hm.of_equiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  by_cases hvx : v.type = x.type
  · exact transport v hvx (.linear nv hnv hmv)
  · have htx : t.type = x.type := by
      cases hv : v.type <;> cases ht : t.type <;> cases hx : x.type <;> simp_all
    exact transport t htx (.linear nt hnt hmt)

/-- The original noncommuting bound, with every earlier setup premise discharged. -/
theorem reduced_intrinsic_noncommuting_bound (h : HypothesisF11 L S)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    b F = 1 ∨ b F = 2 := by
  let ht := reduced_triple h
  have hp : 0 < b F := source_b_positive ht
  by_cases hb : b F ≤ 2
  · omega
  have hb₂ : 2 < b F := by omega
  have heven := (reduced_long_critical_even h hc hne hb₂).2
  have hn₄ : b F ≠ 4 := by
    intro hb₄
    have hwv : w ≠ v := by
      intro he
      have hh := hc.1
      rw [he,SimpleGraph.dist_self] at hh
      omega
    obtain ⟨u,hvu,hdu⟩ := exists_predecessor F ht.generate w v hwv
    rw [SimpleGraph.dist_comm (u := w) (v := u),
      SimpleGraph.dist_comm (u := w) (v := v),hc.1] at hdu
    have huw : u ≠ w := by intro he; rw [he,SimpleGraph.dist_self] at hdu; omega
    obtain ⟨t,hwt,hut⟩ := exists_predecessor F ht.generate u w huw
    have hutdist : (graph F).dist u t = 2 := by omega
    have hutne : u ≠ t := by intro he; rw [he,SimpleGraph.dist_self] at hutdist; omega
    obtain ⟨m,htm,hum⟩ := exists_predecessor F ht.generate u t hutne
    have humadj : (graph F).Adj u m := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
    have hdt : (graph F).dist v t + 1 = b F := by
      have h₁ := (connected_graph ht).dist_triangle (u := v) (v := u) (w := t)
      have h₂ := (connected_graph ht).dist_triangle (u := v) (v := t) (w := w)
      have hvud := SimpleGraph.dist_eq_one_iff_adj.mpr hvu
      have htwd := SimpleGraph.dist_eq_one_iff_adj.mpr hwt.symm
      have hvw := hc.1
      omega
    have h₀ := (reduced_long_critical_forward_identities h hc hne hb₂ hvu hdu).1
    have hrev := (reduced_noncommuting_critical_intersections h hc hne).1
    have h₁ := (reduced_long_critical_forward_identities h hrev (by rwa [commutator_comm])
      hb₂ hwt (by rwa [SimpleGraph.dist_comm])).1
    rw [commutator_comm] at h₁
    exact graph_neighbor_centers_ne ht humadj.symm htm.symm hutne (h₀.symm.trans h₁)
  have hb₄ : 4 < b F := by obtain ⟨n,hn⟩ := heven; omega
  exact (Noncommuting.Reduction.reduced_noncommuting_source_conclusion h
    (reduced_long_actor_models h hc hne hb₄)
    (fun x y he => reduced_graph_core_obstruction h y x he.symm) hc hne).1

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
