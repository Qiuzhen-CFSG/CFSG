module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoResidualPairing
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanDistinctSource

/-!
# Vanishing of the terminal path residual core

This module completes the nonsolvable-alpha branch of DGS85 (10.8): the
Cartan commutator escape and normalized two-core generation force the residual
to centralize the full endpoint intersection, while the original endpoint
centralizer calculation identifies its image and gives the contradiction.
Source: DGS, *Groups and Graphs* (1985), (10.8), printed pp.160--161.
-/
public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

theorem original_bTwo_cartan_residual_vanishing
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    (K : Subgroup (G₀ L S)) [IsMulCommutative K]
    (hKE : K ≤ stabilizer F α ⊓ stabilizer F β)
    (hKt : K ≤ stabilizer F t) (hKu : K ≤ stabilizer F u)
    (hd : Disjoint K ((stabilizer F α ⊓ stabilizer F β).pCoreIn 2))
    (hgen : K ⊔ (stabilizer F α ⊓ stabilizer F β).pCoreIn 2 =
      stabilizer F α ⊓ stabilizer F β)
    (ho : Odd (Nat.card K))
    (g : G₀ L S) (hg : g ∈ graphLocalGroup F α)
    (hgK : g ∈ normalizer (K : Set (G₀ L S))) (hgt : g • β = t)
    (a : G₀ L S) (hau : a • α = u)
    (T : Subgroup (G₀ L S)) (hTK : T ≤ K ⊓ graphLocalGroup F β) (hTne : T ≠ ⊥)
    (hW : (Z F u ⊔ Z F (g • u)) ⊔ Q F α = graphLocalGroup F α)
    (hthree : ⁅V F β 1 ⊓ Q F α,T⁆ ≤
      centralizer ((bTwoResidual F β t u (g • u) ⊓ Q F y : Subgroup (G₀ L S)) : Set (G₀ L S))) :
    bTwoResidual F β t u (g • u) ⊓ Q F y = ⊥ := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hB := reduced_borel_core_sylow h
  have hS := reduced_vertex_sylow h
  have hSyl := reduced_kernel_sylow h
  let X := V F β 1 ⊓ Q F α
  let M := ⁅X,T⁆
  let R := bTwoResidual F β t u (g • u)
  let A := R ⊓ Q F y
  have nQ (v : Vertex F) : stabilizer F v ≤ normalizer (Q F v : Set (G₀ L S)) :=
    CommutingNontrivial.stabilizer_normalizes_Q F v
  have hnX : K ≤ normalizer (X : Set (G₀ L S)) :=
    (le_inf ((hKE.trans inf_le_right).trans (graph_stabilizer_normalizes_V H β 1))
      ((hKE.trans inf_le_left).trans (nQ α))).trans inf_normalizer_le_normalizer_inf
  have hnT : K ≤ normalizer (T : Set (G₀ L S)) :=
    ((le_centralizer K).trans (centralizer_le (hTK.trans inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hnM : K ≤ normalizer (M : Set (G₀ L S)) := by
    intro k hk
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hnX hk),
      mem_normalizer_iff_map_conj_eq.mp (hnT hk)]
  have hMX : M ≤ X := le_normalizer_iff_commutator_le_left.mp ((hTK.trans inf_le_left).trans hnX)
  have hXβ : X ≤ Q F β := inf_le_left.trans (graph_V_le_Q_of_short H hSyl β (by rw [hb]; decide))
  have hXα : X ≤ Q F α := inf_le_right
  have hME : M ≤ (stabilizer F t ⊓ stabilizer F α).pCoreIn 2 := by
    rw [inf_comm]
    exact hMX.trans (hXα.trans (graph_Q_le_edgeCore H ht))
  have hMne : ¬ M ≤ Q F t := by
    intro hm
    exact original_bTwo_cartan_commutator_escape h hc hne hb hβu ht htne hns K
      hKE hKt hKu hd hgen ho g hg hgK hgt a hau T hTK hTne
      (le_inf (hMX.trans hXβ) hm)
  have hKta : K ≤ stabilizer F t ⊓ stabilizer F α := le_inf hKt (hKE.trans inf_le_left)
  obtain ⟨hdt,hgent⟩ := CommutingTrivial.path_cartan_complement_at_edge H hab ht.symm
    K hKE hKta ho hd hgen
  obtain ⟨n,hn,J,fJ,finJ,hJ,⟨eJ⟩⟩ := reduced_noncommuting_actor_quotients_linear h hc hne t
  let _ := fJ
  let _ := finJ
  let _ : Fintype J := Fintype.ofFinite J
  let _ : CharP J 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hJ)
  let et := eJ.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi J)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hMtwo : IsPGroup 2 M := (isPGroup_pCoreIn 2 (stabilizer F t ⊓ stabilizer F α)).of_injective
    (inclusion hME) (inclusion_injective _)
  have hspan := cartan_normalized_two_subgroup_core_product H hB hS ht.symm et K M
    hKta hdt hgent hME hMtwo hnM hMne
  have hMQ : M ≤ normalizer (Q F t : Set (G₀ L S)) :=
    (hME.trans ((pCoreIn_le 2 _).trans inf_le_left)).trans (nQ t)
  have hXspan : X ≤ M ⊔ D F β t := by
    intro x hx
    have hxprod : x ∈ (M : Set (G₀ L S)) * (Q F t : Set (G₀ L S)) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hMQ,hspan,inf_comm]
      exact graph_Q_le_edgeCore H ht (hXα hx)
    obtain ⟨m,hm,q,hq,rfl⟩ := hxprod
    have hqX : q ∈ X := by
      simpa only [inv_mul_cancel_left] using X.mul_mem (X.inv_mem (hMX hm)) hx
    exact (M ⊔ D F β t).mul_mem (mem_sup_left hm) (mem_sup_right ⟨hXβ hqX,hq⟩)
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let _ : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hω := c.omega_eq_bot_of_central_neighbor H hB hS hactor hcentral
  obtain ⟨_,_,hDα,_,hD,_,_,_⟩ := c.central_D_structure H hSyl hb hω ht htne
  let _ := hD
  have hAD : A ≤ D F β t := inf_le_left.trans inf_le_left
  have hDC : D F β t ≤ centralizer (A : Set (G₀ L S)) :=
    (le_centralizer (D F β t)).trans (centralizer_le hAD)
  have hXC : X ≤ centralizer (A : Set (G₀ L S)) := hXspan.trans (sup_le hthree hDC)
  have hIC : Q F α ⊓ Q F β ≤ centralizer (A : Set (G₀ L S)) := by
    rw [c.seed_adjacent_intersection H hSyl hb ht htne]
    exact sup_le hXC hDC
  obtain ⟨m,hm,B,fB,finB,hBcard,⟨eB⟩⟩ := reduced_noncommuting_actor_quotients_linear h hc hne β
  let _ := fB
  let _ := finB
  let _ : Fintype B := Fintype.ofFinite B
  let _ : CharP B 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hBcard)
  let eβ := eB.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi B)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hQam : (Q F α).map ι = (parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  have hQbm : (Q F β).map ι = (parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  have hLam : (graphLocalGroup F α).map ι = enlargedEndpoint L S 0 :=
    reduced_graphLocalGroup_image h false
  have hDm : (D F β t).map ι = (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι := by
    change (Q F β ⊓ Q F t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQbm]
  have hDorig : IsElementaryAbelian 2
      ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι : Subgroup G) := by
    rw [←hDm]
    exact IsElementaryAbelian.map ι
  let g' : c.actor := ⟨g,hactor.symm ▸ hg⟩
  have hWorig : ((Z F u).map ι ⊔ (Z F (g • u)).map ι) ⊔
      (parabolic L S 0).pCoreIn 2 = enlargedEndpoint L S 0 := by
    have hh := congrArg (map ι) hW
    rw [Subgroup.map_sup,Subgroup.map_sup,hQam,hLam] at hh
    exact hh
  have hpair := original_bTwo_residual_endpoint_centralizer h hc hne hb hβu ht htne
    c hactor eβ g' hgt hWorig hDorig
  have hRm : R.map ι =
      ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι) ⊓
        centralizer (((Z F u).map ι ⊔ (Z F (g • u)).map ι : Subgroup G) : Set G) := by
    change (D F β t ⊓ centralizer ((Z F u ⊔ Z F (g • u) : Subgroup (G₀ L S)) : Set (G₀ L S))).map ι = _
    rw [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,hDm,Subgroup.map_sup]
  have hIm : (Q F α ⊓ Q F β).map ι =
      (parabolic L S 0).pCoreIn 2 ⊓ (parabolic L S 1).pCoreIn 2 := by
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQam,hQbm]
  have hzero : R ⊓ centralizer ((Q F α ⊓ Q F β : Subgroup (G₀ L S)) : Set (G₀ L S)) = ⊥ := by
    apply map_injective (G₀ L S).subtype_injective
    rw [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,hRm,hIm,Subgroup.map_bot]
    exact hpair
  exact bot_unique ((le_inf inf_le_left (le_centralizer_iff.mp hIC)).trans hzero.le)

/-- The original nonsolvable-alpha source has a nontrivial path residual
whose intersection with the prescribed terminal core is trivial. All Cartan,
local-action, distinctness and escape premises are discharged. -/
theorem original_bTwo_path_cartan_residual_trivial
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0)) :
    let E := stabilizer F α ⊓ stabilizer F β
    ∃ K : Subgroup (G₀ L S),
      K ≤ stabilizer F t ⊓ stabilizer F α ⊓ stabilizer F β ⊓
        stabilizer F u ⊓ stabilizer F y ∧
      Disjoint K (E.pCoreIn 2) ∧ K ⊔ E.pCoreIn 2 = E ∧
      Odd (Nat.card K) ∧ IsMulCommutative K ∧
      K = (K ⊓ graphLocalGroup F α) ⊔ (K ⊓ graphLocalGroup F β) ∧
      ∃ g ∈ graphLocalGroup F α, g ∈ normalizer (K : Set (G₀ L S)) ∧ g • β = t ∧
      ∃ a ∈ graphLocalGroup F β, a ∈ normalizer (K : Set (G₀ L S)) ∧ a • α = u ∧
      let W := Z F u ⊔ Z F (g • u)
      let R := bTwoResidual F β t u (g • u)
      let J := R ⊓ Q F y
      W ⊔ Q F α = graphLocalGroup F α ∧
      R = (D F β t ⊓ Q F u) ⊓ Q F (g • u) ∧
      D F β t = Z F α ⊔ R ∧ Disjoint (Z F α) R ∧
      Disjoint R (Z F u) ∧
      K ≤ normalizer (W : Set (G₀ L S)) ⊓ normalizer (R : Set (G₀ L S)) ⊓
        normalizer (J : Set (G₀ L S)) ∧
      R ≤ centralizer ((K ⊓ graphLocalGroup F α : Subgroup (G₀ L S)) : Set (G₀ L S)) ∧
      J ≤ centralizer (((K ⊓ graphLocalGroup F α) ⊔
        (K ⊓ graphLocalGroup F u) : Subgroup (G₀ L S)) : Set (G₀ L S)) ∧
      ⁅V F β 1 ⊓ Q F α, ((K ⊓ graphLocalGroup F α) ⊔
        (K ⊓ graphLocalGroup F u)) ⊓ (K ⊓ graphLocalGroup F β)⁆ ≤
          centralizer (J : Set (G₀ L S)) ∧
      (K ⊓ graphLocalGroup F α).conjBy a = K ⊓ graphLocalGroup F u ∧
      R ≠ ⊥ ∧ J = ⊥ := by
  obtain ⟨K,hfix,hd,hgen,ho,hcomm,hprod,g,hg,hgK,hgt,a,ha,haK,hau,
    hW,hR,hdec,hdis,hdisu,hKn,hRC,hJC,hthree,hconj⟩ :=
      original_bTwo_path_cartan_residual h hc hne hb hβu ht htne hy hyne
  let _ := hcomm
  have hKE : K ≤ stabilizer F α ⊓ stabilizer F β :=
    le_inf (fun k hk => (hfix hk).1.1.1.2) (fun k hk => (hfix hk).1.1.2)
  have hKt : K ≤ stabilizer F t := fun k hk => (hfix hk).1.1.1.1
  have hKu : K ≤ stabilizer F u := fun k hk => (hfix hk).1.2
  let T := ((K ⊓ graphLocalGroup F α) ⊔ (K ⊓ graphLocalGroup F u)) ⊓
    (K ⊓ graphLocalGroup F β)
  have hTne : T ≠ ⊥ := (original_bTwo_cartan_tori_distinct h hc hne hb hβu ht htne
    hns K hKE hd hgen ho g hg hgK hgt a ha haK hau).2
  have hz := original_bTwo_cartan_residual_vanishing h hc hne hb hβu ht htne hns
    K hKE hKt hKu hd hgen ho g hg hgK hgt a hau T inf_le_right hTne hW hthree
  have hRne : bTwoResidual F β t u (g • u) ≠ ⊥ := by
    intro hr
    obtain ⟨k,f,fin,ch,alg,c,hactor,hk,n,hn,hm,hpow,hext,hDne,_⟩ :=
      original_core_layers h hc hne hb hβu ht htne hns
    apply hDne
    have hdZ : D F β t = Z F α := by
      change D F β t = Z F α ⊔ bTwoResidual F β t u (g • u) at hdec
      simpa only [hr,sup_bot_eq] using hdec
    have he := congrArg (map ι) hdZ
    change (Q F β ⊓ Q F t).map ι = (Z F α).map ι at he
    have hQbm : (Q F β).map ι = (parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQbm] at he
    exact he
  exact ⟨K,hfix,hd,hgen,ho,hcomm,hprod,g,hg,hgK,hgt,a,ha,haK,hau,
    hW,hR,hdec,hdis,hdisu,hKn,hRC,hJC,hthree,hconj,hRne,hz⟩


/-- Terminal-core separation in the original completion, with the same
direct-product residual and the literal full original parabolic cores. -/
theorem original_bTwo_path_cartan_separation
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0)) :
    ∃ g ∈ graphLocalGroup F α, g • β = t ∧
      let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι
      let W₀ := (Z F u).map ι ⊔ (Z F (g • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      W₀ ⊔ (parabolic L S 0).pCoreIn 2 = enlargedEndpoint L S 0 ∧
      R₀ = (D₀ ⊓ (Q F u).map ι) ⊓ (Q F (g • u)).map ι ∧
      D₀ = (Z F α).map ι ⊔ R₀ ∧ Disjoint ((Z F α).map ι) R₀ ∧
      R₀ ≠ ⊥ ∧ R₀ ⊓ (Q F y).map ι = ⊥ := by
  obtain ⟨K,hfix,hd,hgen,ho,hcomm,hprod,g,hg,hgK,hgt,a,ha,haK,hau,
    hW,hR,hdec,hdis,hdisu,hKn,hRC,hJC,hthree,hconj,hRne,hzero⟩ :=
      original_bTwo_path_cartan_residual_trivial h hc hne hb hβu ht htne hy hyne hns
  let R := bTwoResidual F β t u (g • u)
  let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι
  let W₀ := (Z F u).map ι ⊔ (Z F (g • u)).map ι
  let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
  have hQam : (Q F α).map ι = (parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  have hQbm : (Q F β).map ι = (parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  have hLam : (graphLocalGroup F α).map ι = enlargedEndpoint L S 0 :=
    reduced_graphLocalGroup_image h false
  have hDm : (D F β t).map ι = D₀ := by
    change (Q F β ⊓ Q F t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQbm]
  have hRm : R.map ι = R₀ := by
    change (D F β t ⊓ centralizer ((Z F u ⊔ Z F (g • u) : Subgroup (G₀ L S)) : Set (G₀ L S))).map ι = _
    rw [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,hDm,Subgroup.map_sup]
  refine ⟨g,hg,hgt,?_,?_,?_,?_,?_,?_⟩
  · have hh := congrArg (map ι) hW
    rw [Subgroup.map_sup,Subgroup.map_sup,hQam,hLam] at hh
    exact hh
  · have hh := congrArg (map ι) hR
    change R.map ι = _ at hh
    rw [hRm,map_inf _ _ _ (G₀ L S).subtype_injective,
      map_inf _ _ _ (G₀ L S).subtype_injective,hDm] at hh
    exact hh
  · have hh := congrArg (map ι) hdec
    change (D F β t).map ι = (Z F α ⊔ R).map ι at hh
    rw [hDm,Subgroup.map_sup,hRm] at hh
    exact hh
  · have hh := Subgroup.disjoint_map (G₀ L S).subtype_injective hdis
    change Disjoint ((Z F α).map ι) (R.map ι) at hh
    rwa [hRm] at hh
  · intro hh
    apply hRne
    apply map_injective (G₀ L S).subtype_injective
    rw [Subgroup.map_bot]
    exact hRm.trans hh
  · have hh := congrArg (map ι) hzero
    change (R ⊓ Q F y).map ι = (⊥ : Subgroup (G₀ L S)).map ι at hh
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hRm,Subgroup.map_bot] at hh
    exact hh


end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
