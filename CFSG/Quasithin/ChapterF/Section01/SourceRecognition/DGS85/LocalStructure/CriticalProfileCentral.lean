module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalProfileAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoCentralSource

/-!
# The central middle vertex of a noncommuting distance-two path

If its center were noncentral, the actual 6.5 obstruction and critical
Sylow product would produce a shifted noncommuting critical pair. The
proved center actions at both pairs contradict the Chapter 10 involution
argument. Thus the middle center is central in its intrinsic actor.
The resulting vanishing central kernel and natural edge commutators give
the literal identities of 7.4, without assuming the middle quotient model.

Source: DGS, Groups and Graphs (1985), 7.4, p.128 and 10.3--10.6,
pp.154--158. The distance-two hypothesis is retained throughout.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- The actual middle center is central: both shifted center actions and
the adjacent-core obstruction are constructed from the original F.1.1 data. -/
theorem reduced_bTwo_middle_central (h : HypothesisF11 L S)
    {v m w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    Z F m ≤ centerIn (graphLocalGroup F m) := by
  obtain ⟨k₀,f₀,n₀,ch₀,a₀,c₀,_⟩ := reduced_bTwo_center_action_exists h hc hne hb hvm hmw
  have ha₀ : a₀ = ZMod.algebra k₀ 2 := Subsingleton.elim _ _
  subst a₀
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  by_contra hnc
  obtain ⟨t,ht,_,_,_,_,hc₁,hne₁⟩ := bTwo_shifted_pair_of_noncentral
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    hb hvm hmw hc hne hnc c₀.critical_product
    (fun t ht => reduced_graph_core_obstruction h v t ht.symm)
  obtain ⟨k₁,f₁,n₁,ch₁,a₁,c₁,_⟩ := reduced_bTwo_center_action_exists h hc₁ hne₁ hb hvm.symm ht.symm
  have ha₁ : a₁ = ZMod.algebra k₁ 2 := Subsingleton.elim _ _
  subst a₁
  let : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
  exact bTwo_paired_center_actions_impossible (reduced_triple h)
    (reduced_kernel_sylow h) hb c₀ c₁ (LinearEquiv.refl _ _) (LinearEquiv.refl _ _)
    hc hc₁ hne hne₁

/-- The exact edge seed and both commutator identities at distance two,
with the original intrinsic actors and graph cores. -/
theorem reduced_bTwo_center_identities (h : HypothesisF11 L S)
    {v m w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    Z F m = omegaCenterIn ((stabilizer F v ⊓ stabilizer F m).pCoreIn 2) ∧
      center (graphLocalGroup F v) = ⊥ ∧
      ⁅Z F v,Z F w⁆ = Z F m ∧ ⁅V F m 1,Q F m⁆ = Z F m := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  have hcentral := reduced_bTwo_middle_central h hc hne hb hvm hmw
  obtain ⟨k,f,n,ch,a,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hvm hmw
  obtain ⟨d,hd⟩ := reduced_critical_actor_localData h hc hne hvm
  dsimp only [reducedFamily] at d hd
  have ho : ¬ 2 ∣ d.Pstar.relIndex (stabilizer F v) := by
    rw [hd]
    exact graph_actor_odd_index ht v
  have hω := c.omega_eq_bot_of_central_neighbor ht (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hactor hcentral
  rw [hactor] at hω
  have hcenter : center d.Pstar = ⊥ := local_center_eq_bot_of_omega_eq_bot d (by rwa [hd])
  have hnat := (reduced_critical_natural_centers_and_products h hc hne).1
  have hseed : Z F m = omegaCenterIn ((stabilizer F v ⊓ stabilizer F m).pCoreIn 2) := by
    obtain ⟨T,hT⟩ := source_edge_vertex_sylow ht (reduced_vertex_sylow h) hvm.symm
    have hTe := Theory.GroupTheory.AmalgamGraph.sylow_image_eq_edge_core
      (stabilizer F m) (stabilizer F m ⊓ stabilizer F v) inf_le_left
      (source_edge_core_sylow ht (reduced_borel_core_sylow h) hvm.symm) T hT
    have hz : Z F m ≤ Z F v := center_le_of_central_neighbor ht
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvm hcentral
    have hs := (reduced_graph_center_product h hvm.symm (by
      dsimp only [reducedFamily]
      rw [sup_eq_right.mpr hz]
      exact (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F v)).mp (Z_normal F v))).1 T
    dsimp only [reducedFamily] at hs
    exact hs.trans ((congrArg omegaCenterIn hTe).trans
      (congrArg (fun X : Subgroup (G₀ L S) => omegaCenterIn (X.pCoreIn 2)) (inf_comm _ _)))
  have hQS : Q F m ≤ (stabilizer F v ⊓ stabilizer F m).pCoreIn 2 := by
    simpa only [inf_comm] using graph_Q_le_edgeCore ht hvm.symm
  have hZQ : Z F w ≤ Q F m := graph_Z_le_Q_of_short ht (reduced_kernel_sylow h)
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hmw.symm,hb]; decide)
  have hZesc : ¬ Z F w ≤ Q F v := by
    intro hh
    apply hne
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
    exact hh.trans (graph_Q_centralizes_Z ht v)
  have hQesc : ¬ Q F m ≤ Q F v := by
    intro hh
    apply reduced_graph_core_obstruction h m v hvm.symm
    dsimp only [reducedFamily]
    rw [inf_eq_right.mpr hh]
    exact (stabilizer F m).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hR := graph_natural_edge_commutator ht (reduced_borel_core_sylow h) hvm d ho
    hcenter (by simpa only [hd,reducedFamily] using hnat) (Z F w) (hZQ.trans hQS) hZesc
  have hQ := graph_natural_edge_commutator ht (reduced_borel_core_sylow h) hvm d ho
    hcenter (by simpa only [hd,reducedFamily] using hnat) (Q F m) hQS hQesc
  exact ⟨hseed,by rw [←hd]; exact hcenter,hR.trans hseed.symm,
    graph_radius_one_commutator_of_edge ht hvm (hQ.trans hseed.symm)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
