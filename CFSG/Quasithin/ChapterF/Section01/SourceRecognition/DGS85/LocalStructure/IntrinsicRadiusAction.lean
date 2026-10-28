module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicEpsilonOne
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RadiusSectionGeneration
public import Theory.Representation.BinaryConjugationSection.Descent

/-!
# The intrinsic radius action in the long noncommuting branch

The epsilon-one exclusion gives a central seed at every neighbor of a
critical endpoint when b > 2. The common-normal obstruction then kills
the endpoint's central kernel. Its proved natural action supplies the
literal identities [Z_alpha,Z_alpha'] = Z_beta and [V_beta,Q_beta] = Z_beta.

The latter identity constructs the actual nonzero V_beta/Z_beta action
of L_beta/Q_beta. Its adjacent-center seed proves fixed-space generation;
conjugacy gives this for every Sylow image. The existing neighborhood-kernel
argument gives faithful Sylow action without identifying U_beta with Q_beta.
The full enlarged-quotient bounds apply to this same action, including the
possible order-144 case, so a sharp quadratic index forces a linear quotient.
The source path/index argument that supplies such an actor in the final
long-distance contradiction remains with the Chapter 7 assembly.

Source: DGS, *Groups and Graphs* (1985), 7.4 and 7.5, pp.128--131,
with the fixed-generation correction in 5.12. Original cores, full edge
stabilizers and quotient maps are unchanged; b=2 is never assumed.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Noncommuting
universe u
variable {G : Type u} [Group G]

/-- The actual local actor generates the radius span from an adjacent center. -/
theorem graph_intrinsic_radius_span
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v u : Vertex (family P)} (he : (graph (family P)).Adj v u)
    (hZZ : Z (family P) u ≤ Z (family P) v) :
    conjugateSpanBy (Z (family P) v) (graphLocalGroup (family P) u) = V (family P) u 1 := by
  let := finite_endpoints h
  have hZV : Z (family P) v ≤ V (family P) u 1 :=
    le_iSup_of_le v (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl he.symm)) le_rfl)
  apply le_antisymm (conjugateSpanBy_le hZV
    ((sylowGenerated_le _).trans (graph_stabilizer_normalizes_V h u 1)))
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  rcases (mem_ball_one (family P) u x).mp hx with hx | rfl
  · obtain ⟨g,hg,hgx⟩ := graphLocalGroup_transitive h hB hS u ⟨v,he.symm⟩ ⟨x,hx⟩
    change g • v = x at hgx
    rw [←hgx,Z_translate]
    rintro _ ⟨z,hz,rfl⟩
    exact subset_closure ⟨g,hg,z,hz,rfl⟩
  · exact hZZ.trans (le_conjugateSpanBy _ _)

private theorem generated_on_every_sylow
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (T R : Sylow 2 D)
    (hg : GeneratedByFixedSpace σ T) : GeneratedByFixedSpace σ R := by
  obtain ⟨g,hgR⟩ := MulAction.exists_smul_eq D T R
  have he : (T : Subgroup D).map (MulAut.conj g).toMonoidHom = (R : Subgroup D) :=
    congrArg Sylow.toSubgroup hgR
  rw [←he]
  apply generatedByFixedSpace_of_equivariant_surjection σ σ
    (MulAut.conj g).toMonoidHom (σ g) ?_ ?_ T hg
  · intro w
    exact ⟨σ g⁻¹ w,σ.self_inv_apply g w⟩
  · intro a w
    simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,MulAut.conj_apply,
      map_mul,Module.End.mul_apply,σ.inv_self_apply]

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- A long noncommuting pair has trivial center in its critical endpoint actor. -/
theorem reduced_long_critical_center_trivial (h : HypothesisF11 L S)
    {v w u : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 2 < b F) (hvu : (graph F).Adj v u) :
    center (graphLocalGroup F v) = ⊥ := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  obtain ⟨c,hcL⟩ := reduced_critical_actor_localData h hc hne hvu
  change c.Pstar = graphLocalGroup F v at hcL
  have ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer F v) := by
    rw [hcL]
    exact graph_actor_odd_index ht v
  have hs := reduced_long_critical_neighbor_seed h hc hne hb hvu
  have hΩ := local_omega_le_edgeSeed c ho (source_edge_core_sylow ht (reduced_borel_core_sylow h) hvu)
  have hΩZ : omegaCenterIn c.Pstar ≤ Z F u := hΩ.trans_eq hs.1.symm
  rw [←hcL]
  apply local_center_eq_bot_of_omega_eq_bot c
  apply graph_local_common_normal_eq_bot ht hvu c.Pstar (graphLocalGroup F u)
    (omegaCenterIn c.Pstar) (local_star_factor c)
  · intro a ha
    simpa only [reducedFamily,inf_comm] using graph_intrinsic_edge_factor ht (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hvu.symm a ha
  · exact hΩ.trans (map_subtype_le _ |>.trans (pCoreIn_le 2 _))
  · apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    exact fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).2.1
  · apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    exact fun z hz => ((mem_omegaCenterIn_iff _ _).mp (hs.2 ▸ hΩZ hz)).2.1

/-- The exact forward-edge commutator identities, with no opposite actor model. -/
theorem reduced_long_critical_forward_identities (h : HypothesisF11 L S)
    {v w u : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 2 < b F) (hvu : (graph F).Adj v u) (hdu : (graph F).dist u w + 1 = b F) :
    ⁅Z F v,Z F w⁆ = Z F u ∧ ⁅V F u 1,Q F u⁆ = Z F u ∧
      ⁅Z F v,(stabilizer F v ⊓ stabilizer F u).pCoreIn 2⁆ = Z F u := by
  let ht := reduced_triple h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  obtain ⟨c,hcL⟩ := reduced_critical_actor_localData h hc hne hvu
  change c.Pstar = graphLocalGroup F v at hcL
  have ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer F v) := by
    rw [hcL]
    exact graph_actor_odd_index ht v
  have hcenter : center c.Pstar = ⊥ := by
    rw [hcL]
    exact reduced_long_critical_center_trivial h hc hne hb hvu
  have hnat : HasNaturalCenter c.Pstar (Z F v) (Q F v) := by
    rw [hcL]
    exact (reduced_critical_natural_centers_and_products h hc hne).1
  have hseed := (reduced_long_critical_neighbor_seed h hc hne hb hvu).1
  have hQS : Q F u ≤ (stabilizer F v ⊓ stabilizer F u).pCoreIn 2 := by
    simpa only [reducedFamily,inf_comm] using graph_Q_le_edgeCore ht hvu.symm
  have hZQ : Z F w ≤ Q F u :=
    graph_Z_le_Q_of_short ht (reduced_kernel_sylow h) (by rw [SimpleGraph.dist_comm]; omega)
  have hZesc : ¬ Z F w ≤ Q F v := by
    intro hh
    apply hne
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
    exact hh.trans (graph_Q_centralizes_Z ht v)
  have hQesc : ¬ Q F u ≤ Q F v := by
    intro hh
    apply reduced_graph_core_obstruction h u v hvu.symm
    dsimp only [reducedFamily]
    rw [inf_eq_right.mpr hh]
    exact (stabilizer F u).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hR := graph_natural_edge_commutator ht (reduced_borel_core_sylow h) hvu c ho
    hcenter hnat (Z F w) (hZQ.trans hQS) hZesc
  have hQ := graph_natural_edge_commutator ht (reduced_borel_core_sylow h) hvu c ho
    hcenter hnat (Q F u) hQS hQesc
  have hS := graph_natural_edge_commutator ht (reduced_borel_core_sylow h) hvu c ho
    hcenter hnat _ le_rfl (fun hh => hQesc (hQS.trans hh))
  exact ⟨hR.trans hseed.symm,graph_radius_one_commutator_of_edge ht hvu
    (hQ.trans hseed.symm),hS.trans hseed.symm⟩

/-- Construct the literal nonzero radius quotient action, its full-edge Sylow,
fixed-space generation at every Sylow and faithfulness on every Sylow image. -/
theorem reduced_long_critical_radius_action (h : HypothesisF11 L S)
    {v w u : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 2 < b F) (hvu : (graph F).Adj v u) (hdu : (graph F).dist u w + 1 = b F) :
    let M := graphLocalGroup F u
    let : ((Q F u).subgroupOf M).Normal := by
      rw [graph_intrinsic_core (reduced_triple h) u]
      infer_instance
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      ∃ (σ : Representation (ZMod 2) (M ⧸ (Q F u).subgroupOf M) W)
        (_s : BinaryConjugationSection M (V F u 1) (Z F u)
          (σ.comp (QuotientGroup.mk' ((Q F u).subgroupOf M)))),
        Nontrivial W ∧ Finite W ∧
        ∃ T : Sylow 2 M,
          (T : Subgroup M).map M.subtype = (stabilizer F v ⊓ stabilizer F u).pCoreIn 2 ∧
          (∀ R : Sylow 2 M,
            GeneratedByFixedSpace σ ((R : Subgroup M).map (QuotientGroup.mk' ((Q F u).subgroupOf M)))) ∧
          ∀ R : Sylow 2 M,
            Disjoint σ.ker ((R : Subgroup M).map (QuotientGroup.mk' ((Q F u).subgroupOf M))) := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  dsimp only
  let M := graphLocalGroup F u
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : ((Q F u).subgroupOf M).Normal := by
    rw [graph_intrinsic_core ht u]
    infer_instance
  let π := QuotientGroup.mk' ((Q F u).subgroupOf M)
  let : IsElementaryAbelian 2 (V F u 1) :=
    graph_V_elementary_of_twice_radius_lt ht (reduced_kernel_sylow h) u (by omega : 2*1 < b F)
  let : ((Z F u).subgroupOf (V F u 1)).Normal := inferInstance
  have hVM : V F u 1 ≤ M :=
    pGroup_le_sylowGenerated _ _
      ((graph_V_le_Q_of_short ht (reduced_kernel_sylow h) u (by omega : 1 < b F)).trans
        (pCoreIn_le 2 _)) (IsElementaryAbelian.isPGroup 2 _)
  have hnV : M ≤ normalizer (V F u 1 : Set (G₀ L S)) :=
    (sylowGenerated_le _).trans (graph_stabilizer_normalizes_V ht u 1)
  have hnZ : M ≤ normalizer (Z F u : Set (G₀ L S)) :=
    (sylowGenerated_le _).trans
      ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F u)).mp (Z_normal F u))
  have hcomm := reduced_long_critical_forward_identities h hc hne hb hvu hdu
  obtain ⟨σ,s,_⟩ := exists_descended_actor M (V F u 1) (Z F u) hVM (Z_le_V F u 1)
    hnV hnZ π (QuotientGroup.mk'_surjective _) (by
      intro a ha z hz
      have haQ : (a : G₀ L S) ∈ Q F u := (QuotientGroup.eq_one_iff a).mp ha
      have hh := commutator_mem_commutator haQ hz
      rw [commutator_comm,hcomm.2.1] at hh
      exact hh)
  have hZZ : Z F u ≤ Z F v :=
    (reduced_long_critical_neighbor_seed h hc hne hb hvu).1.le.trans (by
      obtain ⟨c,hcL⟩ := reduced_critical_actor_localData h hc hne hvu
      change c.Pstar = graphLocalGroup F v at hcL
      apply graph_edgeSeed_le_Z ht (reduced_borel_core_sylow h) hvu c
      rw [hcL]
      exact graph_actor_odd_index ht v)
  have hgen := section_generated_by_fixed_seed M (V F u 1) (Z F u) (Z F v)
    ((stabilizer F v ⊓ stabilizer F u).pCoreIn 2) σ π s
    (graph_intrinsic_radius_span ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvu hZZ)
    (by rw [commutator_comm,hcomm.2.2])
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow ht (reduced_vertex_sylow h) hvu.symm
  have hTe : (T : Subgroup (stabilizer F u)).map (stabilizer F u).subtype =
      (stabilizer F v ⊓ stabilizer F u).pCoreIn 2 := by
    simpa only [reducedFamily,inf_comm] using sylow_image_eq_edge_core (stabilizer F u)
      (stabilizer F u ⊓ stabilizer F v) inf_le_left
      (source_edge_core_sylow ht (reduced_borel_core_sylow h) hvu.symm) T hT
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le
    (H := M) (sylowGenerated_le _) (sylow_le_sylowGenerated _ T)
  have hRe := hR.trans hTe
  have hRs : ((stabilizer F v ⊓ stabilizer F u).pCoreIn 2).subgroupOf M = (R : Subgroup M) := by
    rw [←hRe]
    exact comap_map_eq_self_of_injective M.subtype_injective _
  have hnt := graph_terminal_section_nontrivial ht (reduced_kernel_sylow h)
    (v := w) (w := v) (t := u)
    (by rwa [commutator_comm]) hvu (by rwa [SimpleGraph.dist_comm]) s
  let : Finite (V F u 1) := Finite.of_injective
    (inclusion (hVM.trans (sylowGenerated_le _))) (inclusion_injective _)
  refine ⟨_,inferInstance,inferInstance,σ,s,hnt,inferInstance,R,hRe,?_,?_⟩
  · intro R'
    apply generated_on_every_sylow σ
      (R.mapSurjective (f := π) (QuotientGroup.mk'_surjective _))
      (R'.mapSurjective (f := π) (QuotientGroup.mk'_surjective _))
    simpa only [Sylow.coe_mapSurjective,hRs] using hgen
  · exact graph_radius_section_sylow_kernel (H := M) ht (reduced_kernel_sylow h) hvu.symm hZZ
      (sylowGenerated_le _) σ s

private theorem radius_bounds_at_core
    (h : HypothesisF11 L S) (u : Vertex F)
    (N : Subgroup (graphLocalGroup F u)) [N.Normal]
    (hN : N = pCore 2 (graphLocalGroup F u))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) (graphLocalGroup F u ⧸ N) W)
    (T : Sylow 2 (graphLocalGroup F u ⧸ N))
    (A : Subgroup (graphLocalGroup F u ⧸ N))
    (hAT : A ≤ T) (hA : 1 < Nat.card A) (hq : IsQuadratic σ A)
    (hg : ∀ R : Sylow 2 (graphLocalGroup F u ⧸ N), GeneratedByFixedSpace σ R)
    (hd : Disjoint σ.ker (T : Subgroup _)) :
    Nat.card A ≤ Nat.card (W ⧸ fixedSpace σ A) ∧
      (Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A →
        ∃ n, 0 < n ∧ ClassicalGroup.IsPSL (graphLocalGroup F u ⧸ N) 2 (2^n)) := by
  subst N
  exact reduced_graph_quadratic_bounds h u σ T A hAT hA hq hg hd

/-- Apply the full enlarged-quotient estimates to the constructed radius action.
Every nontrivial quadratic actor has the lower index bound, and a sharp index
forces the literal opposite local quotient to be linear. No model, action,
fixed-generation or Sylow-faithfulness premise is imposed on the source graph. -/
theorem reduced_long_critical_radius_comparison (h : HypothesisF11 L S)
    {v w u : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 2 < b F) (hvu : (graph F).Adj v u) (hdu : (graph F).dist u w + 1 = b F) :
    let M := graphLocalGroup F u
    let : ((Q F u).subgroupOf M).Normal := by
      rw [graph_intrinsic_core (reduced_triple h) u]
      infer_instance
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      ∃ (σ : Representation (ZMod 2) (M ⧸ (Q F u).subgroupOf M) W)
        (_s : BinaryConjugationSection M (V F u 1) (Z F u)
          (σ.comp (QuotientGroup.mk' ((Q F u).subgroupOf M)))),
        Nontrivial W ∧ Finite W ∧
        ∀ (T : Sylow 2 M) (A : Subgroup (M ⧸ (Q F u).subgroupOf M)),
          A ≤ (T : Subgroup M).map (QuotientGroup.mk' ((Q F u).subgroupOf M)) →
          1 < Nat.card A → IsQuadratic σ A →
          Nat.card A ≤ Nat.card (W ⧸ fixedSpace σ A) ∧
            (Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A →
              ∃ n, 0 < n ∧ ClassicalGroup.IsPSL (M ⧸ (Q F u).subgroupOf M) 2 (2^n)) := by
  dsimp only
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let M := graphLocalGroup F u
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : ((Q F u).subgroupOf M).Normal := by
    rw [graph_intrinsic_core (reduced_triple h) u]
    infer_instance
  obtain ⟨W,hadd,hmodule,σ,s,hnt,hfin,_T₀,_hT₀,hgen,hfaith⟩ :=
    reduced_long_critical_radius_action h hc hne hb hvu hdu
  let := hadd
  let := hmodule
  let := hfin
  let π := QuotientGroup.mk' ((Q F u).subgroupOf M)
  refine ⟨W,hadd,hmodule,σ,s,hnt,hfin,?_⟩
  intro T A hAT hA hq
  apply radius_bounds_at_core h u ((Q F u).subgroupOf M)
    (graph_intrinsic_core (reduced_triple h) u) σ
    (T.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)) A hAT hA hq ?_ (hfaith T)
  intro R
  obtain ⟨R,rfl⟩ := Sylow.mapSurjective_surjective (f := π) (QuotientGroup.mk'_surjective _) 2 R
  exact hgen R

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
