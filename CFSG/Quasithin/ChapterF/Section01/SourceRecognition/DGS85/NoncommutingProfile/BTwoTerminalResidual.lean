module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictPathSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourTerminalSeparation
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# Terminal separation and the exact strict residual order

DGS (10.8) is completed on the original core images with one opposite-center
conjugator for every terminal continuation. In the nonbinary-alpha branch,
the original linear quotient is nonsolvable, so the established Cartan
argument applies. The critical center is transitive on the other neighbors
of the opposite vertex and centralizes the residual. It therefore propagates
the pathwise separation without changing the residual or its conjugator.
The proved binary-alpha theorem covers the remaining fields.

For the strict case, choose a full odd Cartan fixing the four-core path of
the same residual. Coprime conjugacy moves this Cartan to fix the terminal
vertex by an element of the critical center. That element centralizes the
residual, so its normalizer is preserved. The literal terminal SL₂ quotient
then gives |R_alpha| = q_beta, including binary and unequal fields. The final
original-source consumer discharges the separation premise internally.

The nonbinary-alpha path application also derives nonsolvability from its
original quotient marking and supplies r = 6, s = 7 and odd long-path
fixers. The strict binary path and irreducibility clauses, and the full
Chapter 10 assembly, are not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.8), printed pp.159--162, and (10.10), pp.164--165. All full original
core and reduced-to-original inclusion maps are retained.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private theorem nonbinary_parabolic_not_solvable
    (h : HypothesisF11 L S)
    (e : (L 0⧸pCore 2 (L 0))≃*PSL(2,K)) (hK : Nat.card K≠2) :
    ¬ Group.IsSolvable (parabolic L S 0) := by
  have hfour : 3 < Nat.card K := by
    let : Fintype K := Fintype.ofFinite K
    have heven : Even (Nat.card K) := by
      rw [Nat.card_eq_fintype_card,even_iff_two_dvd]
      exact (CharP.cast_eq_zero_iff K 2 _).mp (FiniteField.cast_card_eq_zero K)
    have hmin : 1 < Nat.card K := Finite.one_lt_card
    obtain ⟨n,hn⟩ := heven
    omega
  let : Group.IsPerfect PSL(2,K) := GorensteinWalter.psl2_isPerfect_of_card_gt_three K hfour
  intro hs
  let : Group.IsSolvable (L 0⧸pCore 2 (L 0)) :=
    (h.parabolic_solvable_iff_local_quotient 0).mp hs
  exact Group.IsPerfect.not_isSolvable PSL(2,K)
    (Group.isSolvable_of_surjective (f:=e.toMonoidHom) e.surjective)

private theorem critical_center_transitive
    (h : HypothesisF11 L S) {u y z : Vertex F}
    (hβu : (graph F).Adj β u) (hbTwo : b F=2)
    (hy : (graph F).Adj u y) (hz : (graph F).Adj u z)
    (hyne : y≠β) (hzne : z≠β)
    (e : (L 0⧸pCore 2 (L 0))≃*PSL(2,K))
    (hs : Stellmacher.IsSylowSubgroupIn (Z F α⊔Q F u) (stabilizer F u)) :
    ∃ a∈Z F α, a • y=z := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hut : u.type=false := by
    have hh := hβu.1
    change true≠u.type at hh
    cases hu : u.type
    · rfl
    · exact False.elim (hh hu.symm)
  obtain ⟨a,ha⟩ := Subgroup.CosetGeometry.exists_smul_base F u
  rw [hut] at ha
  have hai : a⁻¹ • u=α := by rw [←ha,inv_smul_smul]
  have adj {v : Vertex F} (hv : (graph F).Adj u v) :
      (graph F).Adj α (a⁻¹ • v) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F a⁻¹).map_adj_iff.mpr hv
    change (graph F).Adj (a⁻¹ • u) (a⁻¹ • v) at hh
    rwa [hai] at hh
  have neq {v : Vertex F} (hv : v≠β) : a⁻¹ • v≠a⁻¹ • β :=
    fun he => hv (MulAction.injective a⁻¹ he)
  let eSL := e.trans (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL K).symm
  obtain ⟨b,hb,hby⟩ := CommutingThreeProfile.ReducedLayer.linear_incident_core_transitive
    h false eSL (adj hβu.symm) (adj hy) (adj hz) (neq hyne) (neq hzne)
  let E := (stabilizer F β⊓stabilizer F u).pCoreIn 2
  have hbe : a*b*a⁻¹∈E := by
    have hh := mem_map_of_mem (MulAut.conj a).toMonoidHom hb
    rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 (MulAut.conj a).toMonoidHom (MulAut.conj a).injective,
      map_inf _ _ _ (MulAut.conj a).injective,←stabilizer_translate,
      ←stabilizer_translate,smul_inv_smul,ha] at hh
    exact hh
  have hby' : (a*b*a⁻¹) • y=z := by
    rw [mul_smul,mul_smul,hby,smul_inv_smul]
  have hsE : Z F α⊔Q F u=E := by
    obtain ⟨T,hT⟩ := hs
    have hZU : Z F α⊔Q F u≤stabilizer F u⊓stabilizer F β := by
      refine le_inf (hT ▸ map_subtype_le _) ?_
      apply sup_le
      · apply (graph_Z_le_Q_of_short H (reduced_kernel_sylow h) (v:=α) (w:=β) ?_).trans
          (Q_le_stabilizer F β)
        change (graph F).dist α β < DGS85.b F
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr
          (show (graph F).Adj α β from ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩),hbTwo]
        decide
      · exact (source_Z_Q_U H u).2.trans
          ((ballKernel_one_le_edge F hβu.symm).trans inf_le_right)
    have hh := sylow_image_eq_edge_core (stabilizer F u)
      (stabilizer F u⊓stabilizer F β) inf_le_left
      (source_edge_core_sylow H (reduced_borel_core_sylow h) hβu.symm) T (hT ▸ hZU)
    change Z F α⊔Q F u=(stabilizer F β⊓stabilizer F u).pCoreIn 2
    rw [←hT,inf_comm]
    exact hh
  have hn : Z F α≤normalizer (Q F u:Set (G₀ L S)) :=
    (show Z F α≤stabilizer F u from le_sup_left.trans (hsE.le.trans ((pCoreIn_le 2 _).trans inf_le_right))).trans
      (CommutingNontrivial.stabilizer_normalizes_Q F u)
  have hp : a*b*a⁻¹∈(Z F α:Set (G₀ L S))*(Q F u:Set (G₀ L S)) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hn,hsE]
    exact hbe
  obtain ⟨c,hc,d,hd,he⟩ := hp
  have hdy : d • y=y := (source_Z_Q_U H u).2 hd y ((mem_ball_one F u y).mpr (Or.inl hy))
  exact ⟨c,hc,by rw [←he,mul_smul,hdy] at hby'; exact hby'⟩

/-- The critical center propagates separation to every continuation, while
keeping the residual fixed. -/
theorem original_bTwo_terminal_separation_propagates
    (h : HypothesisF11 L S) {u y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (hy : (graph F).Adj u y) (hyne : y≠β)
    (e : (L 0⧸pCore 2 (L 0))≃*PSL(2,K))
    (R : Subgroup (G₀ L S)) (hRQ : R≤Q F α) (hRy : R⊓Q F y=⊥) :
    ∀ z : Vertex F, (graph F).Adj u z → z≠β → R⊓Q F z=⊥ := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have hZC : Z F α≤centralizer (R:Set (G₀ L S)) :=
    le_centralizer_iff.mp (hRQ.trans (graph_Q_centralizes_Z H α))
  intro z hz hzne
  obtain ⟨a,ha,hay⟩ := critical_center_transitive h hβu hb hy hz hyne hzne e c.critical_product
  have hn := (Subgroup.centralizer_le_normalizer (R:Set (G₀ L S))) (hZC ha)
  have hr : R.map (MulAut.conj a).toMonoidHom=R := mem_normalizer_iff_map_conj_eq.mp hn
  have hh := congrArg (map (MulAut.conj a).toMonoidHom) hRy
  rwa [map_inf _ _ _ (MulAut.conj a).injective,hr,←Q_translate,hay,Subgroup.map_bot] at hh

/-- The actual nonbinary-alpha Cartan witness separates the residual at
every terminal continuation and computes its order in the marked beta field. -/
theorem original_bTwo_nonbinary_terminal_residual
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : Nat.card (K false)≠2) :
    ∃ g∈graphLocalGroup F α, g • β=t ∧
      let ι := (G₀ L S).subtype
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let D₀ := (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      W₀⊔Q₀=enlargedEndpoint L S 0 ∧
      R₀=(D₀⊓(Q F u).map ι)⊓(Q F (g • u)).map ι ∧
      D₀=(Z F α).map ι⊔R₀ ∧ Disjoint ((Z F α).map ι) R₀ ∧
      Nat.card R₀=Nat.card (K true) ∧
      ∀ y : Vertex F, (graph F).Adj u y → y≠β → R₀⊓(Q F y).map ι=⊥ := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hns := nonbinary_parabolic_not_solvable h (e false) hK
  have hval : 3≤Nat.card ((graph F).neighborSet u) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three H (reduced_vertex_sylow h) u.type
  obtain ⟨y,hy,hyne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet u) (by rw [←Nat.card_coe_set_eq]; omega) β
  obtain ⟨C,hfix,hd,hgen,ho,hcomm,_,g,hg,hgC,hgt,_,_,_,_,
    hW,hR,hdec,hdis,hdisu,hCn,hRC,hJC,hthree,hconj,hRne,hzero⟩ :=
    Assembly.BTwoSource.original_bTwo_path_cartan_residual_trivial
      h hc hne hb hβu ht htne hy hyne hns
  let R := bTwoResidual F β t u (g • u)
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hω := c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hactor hcentral
  obtain ⟨_,_,hDα,_⟩ := c.central_D_structure H (reduced_kernel_sylow h) hb hω ht htne
  have hsep := original_bTwo_terminal_separation_propagates h hc hne hb hβu hy hyne
    (e false) R (inf_le_left.trans hDα) hzero
  let eG (i : Bool) := (reduced_graphLinearQuotient h i (e i)).trans
    (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (K i)).symm
  have hyt : y.type=true := by
    have hu := hβu.1
    have hy' := hy.1
    change true≠u.type at hu
    cases hut : u.type <;> cases hyt : y.type
    · exact False.elim (hy' (hut.trans hyt.symm))
    · rfl
    · exact False.elim (hu hut.symm)
    · exact False.elim (hu hut.symm)
  have hcard : Nat.card R=Nat.card (K true) := by
    have hh := Assembly.BTwoSource.path_cartan_residual_card h hy hfix hd hgen ho g
      hR hRne (disjoint_iff.mpr hzero) (fun x hx => (hCn hx).1.2)
      (source_linear_quotient_at H K eG y)
    change Nat.card R=Nat.card (K y.type) at hh
    simpa only [hyt] using hh
  let ι := (G₀ L S).subtype
  let D₀ := (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι
  let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
  let R₀ := D₀⊓centralizer (W₀:Set G)
  have hQa : (Q F α).map ι=(parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  have hQb : (Q F β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  have hDm : (D F β t).map ι=D₀ := by
    change (Q F β⊓Q F t).map ι=_
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQb]
  have hRm : R.map ι=R₀ := by
    change (D F β t⊓centralizer ((Z F u⊔Z F (g • u):Subgroup (G₀ L S)):Set (G₀ L S))).map ι=_
    rw [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,hDm,Subgroup.map_sup]
  change (Z F u⊔Z F (g • u))⊔Q F α=graphLocalGroup F α at hW
  change R=(D F β t⊓Q F u)⊓Q F (g • u) at hR
  refine ⟨g,hg,hgt,?_,?_,?_,?_,?_,?_⟩
  · have hh := congrArg (map ι) hW
    rwa [Subgroup.map_sup,Subgroup.map_sup,hQa,reduced_graphLocalGroup_image h false] at hh
  · have hh := congrArg (map ι) hR
    change R.map ι=_ at hh
    rwa [hRm,map_inf _ _ _ (G₀ L S).subtype_injective,
      map_inf _ _ _ (G₀ L S).subtype_injective,hDm] at hh
  · have hh := congrArg (map ι) hdec
    change (D F β t).map ι=(Z F α⊔R).map ι at hh
    rwa [hDm,Subgroup.map_sup,hRm] at hh
  · have hh := Subgroup.disjoint_map (G₀ L S).subtype_injective hdis
    change Disjoint ((Z F α).map ι) (R.map ι) at hh
    rwa [hRm] at hh
  · change Nat.card R₀=Nat.card (K true)
    rw [←hRm,card_map_of_injective (G₀ L S).subtype_injective,hcard]
  · intro z hz hzne
    have hh := congrArg (map ι) (hsep z hz hzne)
    rwa [map_inf _ _ _ (G₀ L S).subtype_injective,hRm,Subgroup.map_bot] at hh

/-- DGS (10.8) on the original cores, for both fields, with one opposite
center conjugator retained for all terminal vertices. -/
theorem original_bTwo_terminal_separation
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i)) :
    ∃ g∈graphLocalGroup F α, g • β=t ∧
      let ι := (G₀ L S).subtype
      let D₀ := (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      ∀ y : Vertex F, (graph F).Adj u y → y≠β → R₀⊓(Q F y).map ι=⊥ := by
  by_cases hK : Nat.card (K false)=2
  · exact original_bTwo_alpha_binary_terminal_separation h hc hne hb hβu ht htne
      (e false) hK (e true)
  · obtain ⟨g,hg,hgt,_,_,_,_,_,hs⟩ :=
      original_bTwo_nonbinary_terminal_residual h hc hne hb hβu ht htne K e hK
    exact ⟨g,hg,hgt,hs⟩

private theorem residual_cartan_fixing_terminal
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (hy : (graph F).Adj u y) (hyne : y≠β)
    (e : (L 0⧸pCore 2 (L 0))≃*PSL(2,K))
    (g : G₀ L S) (hg : g∈graphLocalGroup F α) (hgt : g • β=t)
    (R : Subgroup (G₀ L S)) (hRQ : R≤Q F α)
    (hfour : R=(D F β t⊓Q F u)⊓Q F (g • u)) :
    ∃ C : Subgroup (G₀ L S),
      C≤stabilizer F t⊓stabilizer F α⊓stabilizer F β⊓stabilizer F u⊓stabilizer F y ∧
      Disjoint C ((stabilizer F α⊓stabilizer F β).pCoreIn 2) ∧
      C⊔(stabilizer F α⊓stabilizer F β).pCoreIn 2=stabilizer F α⊓stabilizer F β ∧
      Odd (Nat.card C) ∧ C≤normalizer (R:Set (G₀ L S)) := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hua : u≠α := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self,hb] at hh
    contradiction
  have hga : g • α=α := sylowGenerated_le _ hg
  have hgu : g • u≠α := fun he => hua (MulAction.injective g (he.trans hga.symm))
  have htgu : (graph F).Adj t (g • u) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hβu
    change (graph F).Adj (g • β) (g • u) at hh
    rwa [hgt] at hh
  let p : SimpleGraph.BasedWalk (graph F) 4 u :=
    ⟨⟨β,hβu.symm⟩,⟨⟨α,hab.symm⟩,⟨⟨t,ht⟩,⟨⟨g • u,htgu⟩,PUnit.unit⟩⟩⟩⟩
  have hp : p.Nonbacktracking := ⟨hua.symm,htne,hgu,True.intro⟩
  have hpa : α∈p.vertices := by change α∈[u,β,α,t,g • u]; simp
  have hpb : β∈p.vertices := by change β∈[u,β,α,t,g • u]; simp
  obtain ⟨C,hCp,hd,hgen,ho,hcomm,_⟩ :=
    Assembly.BTwoSource.noncommuting_four_path_cartan h hc hne p hp hab hpa hpb
  let _ := hcomm
  have hCa : C≤stabilizer F α := fun c hc => hCp hc α hpa
  have hCb : C≤stabilizer F β := fun c hc => hCp hc β hpb
  have hCt : C≤stabilizer F t := fun c hc => hCp hc t (by change t∈[u,β,α,t,g • u]; simp)
  have hCu : C≤stabilizer F u := fun c hc => hCp hc u (by change u∈[u,β,α,t,g • u]; simp)
  have hCgu : C≤stabilizer F (g • u) := fun c hc => hCp hc (g • u)
    (by change g • u∈[u,β,α,t,g • u]; simp)
  have nQ (v : Vertex F) := CommutingNontrivial.stabilizer_normalizes_Q F v
  have hCn : C≤normalizer (R:Set (G₀ L S)) := by
    rw [hfour]
    apply (le_inf ?_ (hCgu.trans (nQ _))).trans inf_normalizer_le_normalizer_inf
    apply (le_inf ?_ (hCu.trans (nQ _))).trans inf_normalizer_le_normalizer_inf
    exact (le_inf (hCb.trans (nQ _)) (hCt.trans (nQ _))).trans inf_normalizer_le_normalizer_inf
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have hZa : Z F α≤stabilizer F α := Z_le_stabilizer F α
  have hZQ : Z F α≤Q F α := fun _ hz =>
    ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U H α).1 hz)).1
  have hZb : Z F α≤stabilizer F β :=
    hZQ.trans ((source_Z_Q_U H α).2.trans ((ballKernel_one_le_edge F hab).trans inf_le_right))
  have hZt : Z F α≤stabilizer F t :=
    hZQ.trans ((source_Z_Q_U H α).2.trans ((ballKernel_one_le_edge F ht).trans inf_le_right))
  have hZu : Z F α≤stabilizer F u := by
    obtain ⟨T,hT⟩ := c.critical_product
    exact le_sup_left.trans (hT ▸ map_subtype_le _)
  have hCZ : C≤normalizer (Z F α:Set (G₀ L S)) := hCa.trans
    ((normal_subgroupOf_iff_le_normalizer hZa).mp (Z_normal F α))
  have hZC : Z F α≤centralizer (R:Set (G₀ L S)) :=
    le_centralizer_iff.mp (hRQ.trans (graph_Q_centralizes_Z H α))
  let : Finite (Z F α⊔C:Subgroup (G₀ L S)) := Finite.of_injective
    (inclusion (sup_le hZa hCa)) (inclusion_injective _)
  have hZtwo : IsPGroup 2 (Z F α) :=
    (isPGroup_pCoreIn 2 (stabilizer F α)).of_injective (inclusion hZQ) (inclusion_injective _)
  obtain ⟨q,hq,hfix⟩ := Theory.GroupAction.exists_two_group_conjugate_fixing_point
    (Z F α) C hZtwo ho (Group.isSolvable_of_comm (mul_comm' (M:=C))) hCZ y (by
      intro a ha
      have hay : (graph F).Adj u (a • y) := by
        have hh := (Subgroup.CosetGeometry.translationGraphIso F a).map_adj_iff.mpr hy
        change (graph F).Adj (a • u) (a • y) at hh
        rwa [hCu ha] at hh
      have hayne : a • y≠β := fun he => hyne (MulAction.injective a (he.trans (hCb ha).symm))
      exact critical_center_transitive h hβu hb hy hay hyne hayne e c.critical_product)
  let C' := C.map (MulAut.conj q).toMonoidHom
  have fix (v : Vertex F) (hCv : C≤stabilizer F v) (hZv : Z F α≤stabilizer F v) :
      C'≤stabilizer F v := by
    rintro a ⟨c,hc,rfl⟩
    exact (stabilizer F v).mul_mem ((stabilizer F v).mul_mem (hZv hq) (hCv hc))
      ((stabilizer F v).inv_mem (hZv hq))
  let E := stabilizer F α⊓stabilizer F β
  have hqE : q∈E := ⟨hZa hq,hZb hq⟩
  have hEm : E.map (MulAut.conj q).toMonoidHom=E := mem_normalizer_iff_map_conj_eq.mp (E.le_normalizer hqE)
  have hSm : (E.pCoreIn 2).map (MulAut.conj q).toMonoidHom=E.pCoreIn 2 := by
    rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 (MulAut.conj q).toMonoidHom (MulAut.conj q).injective,hEm]
  refine ⟨C',le_inf (le_inf (le_inf (le_inf (fix t hCt hZt) (fix α hCa hZa))
    (fix β hCb hZb)) (fix u hCu hZu)) hfix,?_,?_,?_,?_⟩
  · have hh := Subgroup.disjoint_map (f:=(MulAut.conj q).toMonoidHom) (MulAut.conj q).injective hd
    change Disjoint C' ((E.pCoreIn 2).map (MulAut.conj q).toMonoidHom) at hh
    rwa [hSm] at hh
  · have hh := congrArg (map (MulAut.conj q).toMonoidHom) hgen
    change (C⊔E.pCoreIn 2).map (MulAut.conj q).toMonoidHom=E.map (MulAut.conj q).toMonoidHom at hh
    rwa [Subgroup.map_sup,hSm,hEm] at hh
  · rw [show C'=C.map (MulAut.conj q).toMonoidHom from rfl,
      card_map_of_injective (MulAut.conj q).injective]
    exact ho
  · have hqn := (Subgroup.centralizer_le_normalizer _) (hZC hq)
    rintro a ⟨c,hc,rfl⟩
    exact (normalizer (R:Set (G₀ L S))).mul_mem
      ((normalizer _).mul_mem hqn (hCn hc)) ((normalizer _).inv_mem hqn)

/-- Separation computes the order of the actual strict residual in every
field, by a full Cartan normalized on the same four-core intersection. -/
theorem original_bTwo_residual_order_of_separation
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (hy : (graph F).Adj u y) (hyne : y≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (g : G₀ L S) (hg : g∈graphLocalGroup F α) (hgt : g • β=t)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map (G₀ L S).subtype≠
      (Z F α).map (G₀ L S).subtype)
    (hzero : bTwoResidual F β t u (g • u)⊓Q F y=⊥) :
    Nat.card (bTwoResidual F β t u (g • u))=Nat.card (K true) := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hω := c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hactor hcentral
  let g' : c.actor := ⟨g,hactor.symm ▸ hg⟩
  have hop : c.quotient g'∉normalizer (c.imageSylow:Set SL(2,k)) := by
    intro he
    exact htne (hgt.symm.trans (c.normalizer_fixes_neighbor H g' he))
  obtain ⟨d,hdactor,_⟩ := c.exists_oppositeGeometry H (reduced_kernel_sylow h) hb g' hgt hop
  let R := bTwoResidual F β t u (g • u)
  have hr : d.residual=R := d.residual_eq_source H (reduced_kernel_sylow h) hb (hdactor.symm ▸ hω)
  have hfour : R=(D F β t⊓Q F u)⊓Q F (g • u) := hr.symm
  have hdec : D F β t=Z F α⊔R := by
    rw [←hr]
    exact d.decomposition H (reduced_kernel_sylow h) hb
  have hRne : R≠⊥ := by
    intro he
    have hDZ : D F β t=Z F α := by simpa only [he,sup_bot_eq] using hdec
    apply hD
    have hh := congrArg (map (G₀ L S).subtype) hDZ
    change (Q F β⊓Q F t).map (G₀ L S).subtype=(Z F α).map (G₀ L S).subtype at hh
    rwa [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true] at hh
  obtain ⟨C,hfix,hd,hgen,ho,hn⟩ := residual_cartan_fixing_terminal
    h hc hne hb hβu ht htne hy hyne (e false) g hg hgt R (inf_le_left.trans d.separated) hfour
  let eG (i : Bool) := (reduced_graphLinearQuotient h i (e i)).trans
    (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (K i)).symm
  have hyt : y.type=true := by
    have hu := hβu.1
    have hy' := hy.1
    change true≠u.type at hu
    cases hut : u.type <;> cases hyt : y.type
    · exact False.elim (hy' (hut.trans hyt.symm))
    · rfl
    · exact False.elim (hu hut.symm)
    · exact False.elim (hu hut.symm)
  have hh := Assembly.BTwoSource.path_cartan_residual_card h hy hfix hd hgen ho g
    hfour hRne (disjoint_iff.mpr hzero) hn (source_linear_quotient_at H K eG y)
  change Nat.card R=Nat.card (K y.type) at hh
  simpa only [hyt] using hh

/-- The strict source residual has exactly the beta field order, without
restricting either field. The same original residual is separated from
every terminal core. -/
theorem original_bTwo_strict_terminal_residual
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map (G₀ L S).subtype≠
      (Z F α).map (G₀ L S).subtype) :
    ∃ g∈graphLocalGroup F α, g • β=t ∧
      let ι := (G₀ L S).subtype
      let D₀ := (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      Nat.card R₀=Nat.card (K true) ∧
      ∀ y : Vertex F, (graph F).Adj u y → y≠β → R₀⊓(Q F y).map ι=⊥ := by
  obtain ⟨g,hg,hgt,hsep⟩ := original_bTwo_terminal_separation h hc hne hb hβu ht htne K e
  let H := reduced_triple h
  have hval : 3≤Nat.card ((graph F).neighborSet u) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three H (reduced_vertex_sylow h) u.type
  obtain ⟨y,hy,hyne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet u) (by rw [←Nat.card_coe_set_eq]; omega) β
  let ι := (G₀ L S).subtype
  let D₀ := (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι
  let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
  let R₀ := D₀⊓centralizer (W₀:Set G)
  let R := bTwoResidual F β t u (g • u)
  have hDm : (D F β t).map ι=D₀ := by
    change (Q F β⊓Q F t).map ι=_
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hRm : R.map ι=R₀ := by
    change (D F β t⊓centralizer ((Z F u⊔Z F (g • u):Subgroup (G₀ L S)):Set (G₀ L S))).map ι=_
    rw [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,hDm,Subgroup.map_sup]
  have hzero : R⊓Q F y=⊥ := by
    apply map_injective (G₀ L S).subtype_injective
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hRm,Subgroup.map_bot]
    exact hsep y hy hyne
  have hcard := original_bTwo_residual_order_of_separation
    h hc hne hb hβu ht htne hy hyne K e g hg hgt hD hzero
  refine ⟨g,hg,hgt,?_,hsep⟩
  change Nat.card R₀=Nat.card (K true)
  rw [←hRm,card_map_of_injective (G₀ L S).subtype_injective]
  exact hcard

/-- The nonbinary-alpha source supplies the strict path extrema and odd
long-path fixers. Nonsolvability is derived from the actual original
linear quotient, rather than added to the Chapter 10 assumptions. -/
theorem original_bTwo_nonbinary_strict_path_parameters
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : Nat.card (K false)≠2) :
    HasSourcePathParameters (P:=fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 7 ∧
      ∀ {a d : Vertex F} (p : (graph F).Walk a d),
        IsSourcePath p → 7≤p.length →
          Odd (Nat.card (Theory.GroupTheory.WeakBNPair.RegularTree.pathFixer (X:=G₀ L S) p)) := by
  have hval : 3≤Nat.card ((graph F).neighborSet u) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) u.type
  obtain ⟨y,hy,hyne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet u) (by rw [←Nat.card_coe_set_eq]; omega) β
  exact Assembly.BTwoSource.original_bTwo_strict_path_parameters h hc hne hb hβu
    ht htne hy hyne (nonbinary_parabolic_not_solvable h (e false) hK) K e

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
