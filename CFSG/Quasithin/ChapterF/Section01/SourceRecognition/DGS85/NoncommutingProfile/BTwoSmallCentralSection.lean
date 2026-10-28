module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoMinimalNormalBounds

/-!
# Small central beta sections

In the strict case of DGS, *Groups and Graphs*, printed p.165, a beta-invariant
subgroup of the beta core centralizing the beta enlargement lies in its central
root group. Otherwise its Cartan orbit generates the opposite root quotient;
the two neighboring-core intersections would centralize `D_alpha`, contrary
to the strict residual commutator. The original inclusion maps are retained.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

theorem reduced_bTwo_strict_central_section_le
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (N : Subgroup (G₀ L S)) (hNQ : N≤Q F β)
    (hPN : stabilizer F β≤normalizer (N:Set (G₀ L S)))
    (hNC : N≤centralizer (graphLocalGroup F β:Set (G₀ L S))) : N≤Z F β := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hB := reduced_borel_core_sylow h
  have hSyl := reduced_vertex_sylow h
  have hS := reduced_kernel_sylow h
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  have hω := c.omega_eq_bot_of_central_neighbor H hB hSyl hactor hcentral
  obtain ⟨_,_,hDQ,hnD,hDel,_,_,_⟩ := c.central_D_structure H hS hb hω ht htne
  let _ := hDel
  have hpN : IsPGroup 2 N := (isPGroup_pCoreIn 2 (stabilizer F β)).to_le hNQ
  have hZαQ : Z F α≤Q F β :=
    graph_Z_le_Q_of_short H hS (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab,hb]; decide)
  have hZαL : Z F α≤graphLocalGroup F β := hZαQ.trans
    (by rw [←CommutingTrivial.graphLocalGroup_core H β]; exact pCoreIn_le 2 _)
  have hNα : N≤Q F α := by
    have hh := source_critical_inf_centralizer H hB hSyl hc N hpN
      (hNQ.trans (c.neighbor_core_le.trans c.actor_le))
    rw [inf_eq_left.mpr (hNC.trans (centralizer_le hZαL))] at hh
    exact hh.le.trans inf_le_right
  by_contra hNZ
  have hND : ¬N≤D F β t := by
    intro hND
    apply hNZ
    obtain ⟨T⟩ := Sylow.nonempty (p:=2) (G:=stabilizer F β)
    apply le_trans _ (le_iSup (fun R : Sylow 2 (stabilizer F β) =>
      omegaCenterIn ((R:Subgroup (stabilizer F β)).map (stabilizer F β).subtype)) T)
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨pCoreIn_le_sylow _ T (hNQ hx),
        centralizer_le (sylow_le_sylowGenerated _ T) (hNC hx),
        elemPow_eq_one_of_isElementaryAbelian x (hND hx)⟩
  have hNt : ¬N≤Q F t := fun hh => hND (le_inf hNQ hh)
  have hval : 3≤Nat.card ((graph F).neighborSet u) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three H hSyl u.type
  obtain ⟨y,hy,hyne⟩ := Set.exists_ne_of_one_lt_ncard
    (s:=(graph F).neighborSet u) (by rw [←Nat.card_coe_set_eq]; omega) β
  obtain ⟨C,hfix,hd,hgen,ho,hCcomm,hprod,g,hg,hgC,hgt,rest⟩ :=
    Assembly.BTwoSource.original_bTwo_path_cartan_residual h hc hne hb hβu ht htne hy hyne
  change g • β=t at hgt
  have hCE : C≤stabilizer F α⊓stabilizer F β :=
    le_inf (fun c hc => (hfix hc).1.1.1.2) (fun c hc => (hfix hc).1.1.2)
  have hCt : C≤stabilizer F t⊓stabilizer F α :=
    le_inf (fun c hc => (hfix hc).1.1.1.1) (fun c hc => (hfix hc).1.1.1.2)
  obtain ⟨hdt,hgent⟩ := CommutingTrivial.path_cartan_complement_at_edge H hab ht.symm C hCE hCt ho hd hgen
  obtain ⟨n,hn,K,fK,finK,hK,⟨eK⟩⟩ := reduced_noncommuting_actor_quotients_linear h hc hne t
  let _ := fK
  let _ := finK
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let et := eK.trans (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL K).symm
  have hNS : N≤(stabilizer F t⊓stabilizer F α).pCoreIn 2 :=
    hNα.trans (by simpa only [inf_comm] using graph_Q_le_edgeCore H ht)
  have hNtgen := Assembly.BTwoSource.cartan_normalized_two_subgroup_core_product
    H hB hSyl ht.symm et C N hCt hdt hgent hNS hpN (hCE.trans inf_le_right |>.trans hPN) hNt
  have hnQt : N≤normalizer (Q F t:Set (G₀ L S)) :=
    hNα.trans ((source_Z_Q_U H α).2.trans
      ((ballKernel_one_le_edge F ht).trans inf_le_right) |>.trans
        (CommutingNontrivial.stabilizer_normalizes_Q F t))
  have hI : Q F α⊓Q F β=N⊔D F β t := by
    apply le_antisymm _ (sup_le (le_inf hNα hNQ) (le_inf hDQ inf_le_left))
    intro x hx
    have hxprod : x∈(N:Set (G₀ L S))*(Q F t:Set (G₀ L S)) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hnQt,hNtgen]
      exact (show Q F α≤(stabilizer F t⊓stabilizer F α).pCoreIn 2 from
        by simpa only [inf_comm] using graph_Q_le_edgeCore H ht) hx.1
    obtain ⟨a,ha,z,hz,rfl⟩ := hxprod
    have hzβ : z∈Q F β := by
      simpa only [inv_mul_cancel_left] using (Q F β).mul_mem ((Q F β).inv_mem (hNQ ha)) hx.2
    exact (N⊔D F β t).mul_mem (mem_sup_left ha) (mem_sup_right ⟨hzβ,hz⟩)
  have hQL : Q F β≤graphLocalGroup F β := by
    rw [←CommutingTrivial.graphLocalGroup_core H β]; exact pCoreIn_le 2 _
  have hIC : Q F α⊓Q F β≤centralizer (D F β t:Set (G₀ L S)) := by
    rw [hI]
    exact sup_le (hNC.trans (centralizer_le (inf_le_left.trans hQL))) (le_centralizer _)
  let g' : c.actor := ⟨g,hactor ▸ hg⟩
  have hga : g • α=α := c.actor_le g'.property
  have hDmap : (D F β t).map (MulAut.conj g).toMonoidHom=D F β t :=
    mem_normalizer_iff_map_conj_eq.mp (hnD g'.property)
  have hJC : Q F α⊓Q F t≤centralizer (D F β t:Set (G₀ L S)) := by
    have hh := congrArg (map (MulAut.conj g).toMonoidHom)
      (commutator_eq_bot_iff_le_centralizer.mpr hIC)
    rw [map_commutator,map_inf _ _ _ (MulAut.conj g).injective,←Q_translate,←Q_translate,
      hga,hgt,hDmap,Subgroup.map_bot] at hh
    exact commutator_eq_bot_iff_le_centralizer.mp hh
  obtain ⟨nb,hnb,Kb,fb,finb,hKb,⟨eb⟩⟩ := reduced_bTwo_middle_quotient_linear h hc hne hb hab hβu
  let _ := fb
  let _ := finb
  let : Fintype Kb := Fintype.ofFinite Kb
  let : CharP Kb 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hKb)
  let eβ := eb.trans (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL Kb).symm
  have hQgen : (Q F α⊓Q F β)⊔(Q F α⊓Q F t)=Q F α :=
    (c.seed_eq_core_intersections H hS hb ht htne).symm.trans
      (c.linear_seed_eq_core_and_index H hB hSyl hS hb ht htne hnot eβ).1
  have hQC : Q F α≤centralizer (D F β t:Set (G₀ L S)) := hQgen ▸ sup_le hIC hJC
  have hDne : D F β t≠Z F α := by
    intro he
    apply hD
    have hh := congrArg (map ι) he
    have hQmap : (Q F β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
    simpa only [D,map_inf _ _ _ (G₀ L S).subtype_injective,hQmap] using hh
  have hRcomm := c.strict_residual_core_commutator H hB hSyl hb hactor hcentral ht htne
    hcomm hnot eβ hDne (LinearEquiv.refl _ _) g' hgt
  have hRC : bTwoResidual F β t u (g • u)≤centralizer (Q F α:Set (G₀ L S)) :=
    inf_le_left.trans (le_centralizer_iff.mp hQC)
  rw [commutator_eq_bot_iff_le_centralizer.mpr hRC] at hRcomm
  exact hne (by rw [←hRcomm,commutator_bot_left])

/-- The center argument transported through the actual reduced-to-original inclusion. -/
theorem original_bTwo_strict_central_section_le
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (N : Subgroup G) (hNQ : N≤(parabolic L S 1).pCoreIn 2)
    (hPN : parabolic L S 1≤normalizer (N:Set G))
    (hNC : N≤centralizer (enlargedEndpoint L S 1:Set G)) : N≤(Z F β).map ι := by
  have hQmap : (Q F β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  have hN0 : N≤G₀ L S := hNQ.trans (hQmap.ge.trans (map_subtype_le _))
  let N₀ := N.subgroupOf (G₀ L S)
  have hNm : N₀.map ι=N := map_subgroupOf_eq_of_le hN0
  have hNQ₀ : N₀≤Q F β := by
    apply (map_le_map_iff_of_injective (G₀ L S).subtype_injective).mp
    rw [hNm,hQmap]
    exact hNQ
  have hn : stabilizer F β≤normalizer (N₀:Set (G₀ L S)) := by
    intro x hx
    have hxP : (x:G)∈P₀ L S 1 := by
      rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hx
      exact hx
    exact le_normalizer_comap ι (hPN (P₀_le h 1 hxP))
  have hLmap : (graphLocalGroup F β).map ι=enlargedEndpoint L S 1 :=
    reduced_graphLocalGroup_image h true
  have hnc : N₀≤centralizer (graphLocalGroup F β:Set (G₀ L S)) := by
    intro x hx y hy
    apply (G₀ L S).subtype_injective
    change (y:G)*(x:G)=(x:G)*(y:G)
    exact hNC hx y (hLmap ▸ mem_map_of_mem ι hy)
  have hh := map_mono (f:=ι)
    (reduced_bTwo_strict_central_section_le h hc hne hb hβu ht htne hD N₀ hNQ₀ hn hnc)
  rwa [hNm] at hh

/-- The lower bound on p.165 now excludes small central sections internally. -/
theorem original_bTwo_nonbinary_beta_section_lower
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (N : Subgroup G) (hNQ : N≤(parabolic L S 1).pCoreIn 2)
    (hZN : (Z F β).map ι<N)
    (hPN : parabolic L S 1≤normalizer (N:Set G)) :
    Nat.card (K true)^2≤Nat.card (N⧸((Z F β).map ι).subgroupOf N) := by
  by_contra! hsmall
  have hnc := original_bTwo_nonbinary_beta_small_section_central h hc hne hb hβu ht htne
    K e hK hD N hNQ hZN.le hPN hsmall
  exact (not_le_of_gt hZN) (original_bTwo_strict_central_section_le h hc hne hb hβu ht htne
    hD N hNQ hPN (hnc.trans inf_le_right))

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
