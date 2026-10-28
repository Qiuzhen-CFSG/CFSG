module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoResidualGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoStrictPaths
public import Theory.SpecificGroups.SL2.RootLiftDerived

/-!
# The nonbinary beta actor generates its core by commutators

In the strict branch, the residual generates the beta core under the beta
actor. The seven-path theorem separates any chosen opposite-center residual
from the terminal core, including the transporter normalized by the source
Cartan. Its image is then a full root subgroup at that terminal vertex.
When the beta field has more than two elements, the odd Cartan torus moves
this root subgroup fully. The alpha torus centralizes the residual, so the
beta torus supplies all of it by commutators. Normal generation now yields
[Q_beta,L_beta] = Q_beta.

The literal beta quotient is perfect in this field range. The core
commutator equality lifts perfection to the beta actor and gives
O²(L_beta) = L_beta. Both original-source applications retain the original
endpoint inclusions and quotient markings, with no restriction on the alpha
field. These are the initial steps of DGS, *Groups and Graphs* (1985),
(10.10)(d), printed p.164. The full beta-stabilizer irreducibility argument
on p.165 is a further step.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P

/-- A separated nontrivial two-subgroup normalized by the source Cartan is
fully moved by it when the terminal field is nonbinary. -/
private theorem cartan_separated_root_commutator
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B)=pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype≤B)
    {v w : Vertex F} (hvw : (graph F).Adj v w)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup F v⧸pCore 2 (graphLocalGroup F v))≃*SL(2,k))
    (hk : 2<Nat.card k) (C R : Subgroup G)
    (hCE : C≤stabilizer F v⊓stabilizer F w)
    (hdisC : Disjoint C ((stabilizer F v⊓stabilizer F w).pCoreIn 2))
    (hgenC : C⊔(stabilizer F v⊓stabilizer F w).pCoreIn 2=stabilizer F v⊓stabilizer F w)
    (ho : Odd (Nat.card C))
    (hRS : R≤(stabilizer F v⊓stabilizer F w).pCoreIn 2)
    (hnR : C≤normalizer (R:Set G)) (hRne : R≠⊥) (hdisR : Disjoint R (Q F v)) :
    ⁅R,C⁆=R := by
  let := finite_endpoints h
  let M := graphLocalGroup F v
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker=pCore 2 M := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hcore : (pCore 2 M).map M.subtype=Q F v := CommutingTrivial.graphLocalGroup_core h v
  have hRM : R≤M := hRS.trans (graph_intrinsic_edgeCore_le h)
  have hRp : IsPGroup 2 R :=
    (isPGroup_pCoreIn 2 (stabilizer F v⊓stabilizer F w)).of_injective
      (inclusion hRS) (inclusion_injective _)
  have hcover := (Assembly.BTwoSource.cartan_normalized_disjoint_two_subgroup_card
    h hB hS hvw e C R hCE hdisC hgenC hRS hRp hnR hRne hdisR).1
  obtain ⟨T,hT⟩ := CommutingTrivial.local_edge_sylow h hB hS hvw
  change Sylow 2 M at T
  change (T:Subgroup M).map M.subtype=_ at hT
  let Tq := T.mapSurjective hq
  let R' := R.subgroupOf M
  let C' := (C⊓M).subgroupOf M
  have hRT : R'⊔pCore 2 M=T := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hRM,hcore,hT]
    exact hcover
  have hRim : R'.map q=(Tq:Subgroup SL(2,k)) := by
    have hh := congrArg (Subgroup.map q) hRT
    rw [Subgroup.map_sup,←hker,map_ker_self,sup_bot_eq] at hh
    exact hh
  have hRker : R'⊓q.ker=⊥ := by
    apply bot_unique
    intro r hr
    apply Subtype.ext
    apply disjoint_def.mp hdisR hr.1
    rw [←hcore]
    exact mem_map_of_mem M.subtype (hker ▸ hr.2)
  have hCn : C'≤normalizer (R':Set M) := by
    apply le_normalizer_iff.mpr
    intro c hc r hr
    exact (mem_normalizer_iff.mp (hnR hc.1) (r:G)).mp hr
  have hCo : Odd (Nat.card C') := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show C⊓M≤M from inf_le_right)).toEquiv]
    exact ho.of_dvd_nat (card_dvd_of_le (show C⊓M≤C from inf_le_left))
  have hCimne : C'.map q≠⊥ := by
    intro he
    have hCzero : C'=⊥ := by
      apply bot_unique
      intro c hc
      have hck : c∈q.ker := (Subgroup.map_eq_bot_iff C').mp he hc
      have hcQ : (c:G)∈Q F v := hcore ▸ mem_map_of_mem M.subtype (hker ▸ hck)
      exact Subtype.ext (disjoint_def.mp hdisC hc.1 ((graph_Q_le_edgeCore h hvw) hcQ))
    obtain ⟨⟨eC⟩,_⟩ := CommutingTrivial.edge_complement_local_torus h hB hS hvw e C hCE hdisC hgenC
    have hCc : Nat.card C'=Nat.card kˣ :=
      (Nat.card_congr (subgroupOfEquivOfLe (show C⊓M≤M from inf_le_right)).toEquiv).trans
        (Nat.card_congr eC.toEquiv)
    rw [hCzero,card_bot,Nat.card_units] at hCc
    omega
  have hmove : (⁅R',C'⁆).map q=R'.map q := by
    rw [map_commutator,hRim]
    apply Matrix.SpecialLinearGroup.sylow_commutator_odd_normalizer Tq (C'.map q)
    · change C'.map q≤normalizer ((Tq:Subgroup SL(2,k)):Set SL(2,k))
      rw [←hRim]
      exact (map_mono hCn).trans (R'.le_normalizer_map q)
    · exact hCo.of_dvd_nat (C'.card_map_dvd q)
    · exact hCimne
  have hle : ⁅R',C'⁆≤R' := le_normalizer_iff_commutator_le_left.mp hCn
  have hfull : ⁅R',C'⁆=R' := by
    apply le_antisymm hle
    intro r hr
    obtain ⟨x,hx,hxr⟩ := hmove.symm ▸ mem_map_of_mem q hr
    have he : r*x⁻¹∈R'⊓q.ker := ⟨R'.mul_mem hr (R'.inv_mem (hle hx)),by
      change q (r*x⁻¹)=1
      rw [map_mul,map_inv,hxr,mul_inv_cancel]⟩
    have hrx : r=x := mul_inv_eq_one.mp (mem_bot.mp (hRker ▸ he))
    exact hrx ▸ hx
  have hfullG : ⁅R,C⊓M⁆=R := by
    have hh := congrArg (map M.subtype) hfull
    rwa [map_commutator,map_subgroupOf_eq_of_le hRM,
      map_subgroupOf_eq_of_le (show C⊓M≤M from inf_le_right)] at hh
  exact le_antisymm (le_normalizer_iff_commutator_le_left.mp hnR)
    (hfullG.symm.le.trans (commutator_mono le_rfl inf_le_left))

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open DGS85.Reduction Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.WeakBNPair.RegularTree
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The strict seven-path profile separates the four-core intersection
from the terminal core for every chosen opposite transporter. -/
private theorem strict_terminal_four_core_separation
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (hy : (graph F).Adj u y) (hyne : y≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (g : G₀ L S) (hg : g∈graphLocalGroup F α) (hgt : g • β=t) :
    ((D F β t⊓Q F u)⊓Q F (g • u))⊓Q F y=⊥ := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  obtain ⟨hpar,hodd⟩ := original_bTwo_strict_source_path_parameters h hc hne hb hβu ht htne K e hD
  have hs : sourceS (P:=fun i => (P₀ L S i).subgroupOf (G₀ L S))=7 :=
    (sourceS_spec H (reduced_vertex_sylow h)).2.unique hpar.2
  have hval (v : Vertex F) : 3≤Nat.card ((graph F).neighborSet v) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three H (reduced_vertex_sylow h) v.type
  obtain ⟨z,hyz,hzu⟩ := Set.exists_ne_of_one_lt_ncard
    (s:=(graph F).neighborSet y) (by rw [←Nat.card_coe_set_eq]; have := hval y; omega) u
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hgygu : (graph F).Adj (g • y) (g • u) :=
    (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hy.symm
  have hgut : (graph F).Adj (g • u) t := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hβu
    change (graph F).Adj (g • β) (g • u) at hh
    rw [hgt] at hh
    exact hh.symm
  let p : BasedWalk (graph F) 7 (g • y) :=
    ⟨⟨g • u,hgygu⟩,⟨⟨t,hgut⟩,⟨⟨α,ht.symm⟩,⟨⟨β,hab⟩,
      ⟨⟨u,hβu⟩,⟨⟨y,hy⟩,⟨⟨z,hyz⟩,PUnit.unit⟩⟩⟩⟩⟩⟩⟩
  have hua : u≠α := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self,hb] at hh
    contradiction
  have hgyt : g • y≠t := fun he => hyne (MulAction.injective g (he.trans hgt.symm))
  have hgua : g • u≠α := fun he => hua (MulAction.injective g (he.trans (sylowGenerated_le _ hg).symm))
  have hp : p.Nonbacktracking := ⟨hgyt.symm,hgua.symm,htne.symm,hua,hyne,hzu,True.intro⟩
  have hsimple : p.toWalk.IsPath := Theory.GroupAction.CubicTree.isPath_of_short_rightRegular
    hval 7 (fun m hm v q hq =>
      (sourceS_short_regular H (reduced_vertex_sylow h) q (by omega) hq).2) p le_rfl hp
  have hfix : pathFixer (X:=G₀ L S) p.toWalk=pathStabilizer F p := by
    ext x
    rw [mem_pathFixer_support,support_toWalk]
    rfl
  have ho : Odd (Nat.card (pathStabilizer F p)) := by
    rw [←hfix]
    exact hodd p.toWalk (Or.inl hsimple) (length_toWalk p).ge
  let J := ((D F β t⊓Q F u)⊓Q F (g • u))⊓Q F y
  have hJP : J≤pathStabilizer F p := by
    intro r hr v hv
    have fix (a d : Vertex F) (had : (graph F).Adj a d) (hra : r∈Q F a) : r • d=d :=
      ((source_Z_Q_U H a).2.trans ((ballKernel_one_le_edge F had).trans inf_le_right)) hra
    change v∈[g • y,g • u,t,α,β,u,y,z] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact fix _ _ hgygu.symm hr.1.2
    · exact Q_le_stabilizer F _ hr.1.2
    · exact Q_le_stabilizer F _ hr.1.1.1.2
    · exact fix _ _ hab.symm hr.1.1.1.1
    · exact Q_le_stabilizer F _ hr.1.1.1.1
    · exact Q_le_stabilizer F _ hr.1.1.2
    · exact Q_le_stabilizer F _ hr.2
    · exact fix _ _ hyz hr.2
  let : Finite (pathStabilizer F p) := Finite.of_injective
    (inclusion (pathStabilizer_le F p)) (inclusion_injective _)
  let : Finite J := Finite.of_injective (inclusion hJP) (inclusion_injective _)
  have hJtwo : IsPGroup 2 J := (isPGroup_pCoreIn 2 (stabilizer F β)).of_injective
    (inclusion (show J≤Q F β from fun _ hx => hx.1.1.1.1)) (inclusion_injective _)
  obtain ⟨n,hn⟩ := hJtwo.exists_card_eq
  have hd : Disjoint J (pathStabilizer F p) := disjoint_of_coprime_natCard (by
    rw [hn]
    exact ho.coprime_two_left.pow_left n)
  exact bot_unique ((le_inf le_rfl hJP).trans hd.le_bot)


/-- The original strict nonbinary-beta source satisfies
`[Q_beta,L_beta] = Q_beta`, including the binary-alpha case. -/
theorem original_bTwo_nonbinary_beta_core_commutator
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    ⁅(parabolic L S 1).pCoreIn 2,enlargedEndpoint L S 1⁆=(parabolic L S 1).pCoreIn 2 := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hval : 3≤Nat.card ((graph F).neighborSet u) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three H (reduced_vertex_sylow h) u.type
  obtain ⟨y,hy,hyne⟩ := Set.exists_ne_of_one_lt_ncard
    (s:=(graph F).neighborSet u) (by rw [←Nat.card_coe_set_eq]; omega) β
  obtain ⟨C,hfix,hd,hgen,ho,hCcomm,hprod,g,hg,hgC,hgt,a,ha,haC,hau,
    hW,hfour,hdec,hdis,hdisu,hn,hRC,hJC,hthree,hconj⟩ :=
    Assembly.BTwoSource.original_bTwo_path_cartan_residual h hc hne hb hβu ht htne hy hyne
  let R := bTwoResidual F β t u (g • u)
  change R=(D F β t⊓Q F u)⊓Q F (g • u) at hfour
  change D F β t=Z F α⊔R at hdec
  have hzero : R⊓Q F y=⊥ := by
    rw [hfour]
    exact strict_terminal_four_core_separation h hc hne hb hβu ht htne hy hyne K e hD g hg hgt
  have hQb : (Q F β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  have hDm : (D F β t).map ι=(parabolic L S 1).pCoreIn 2⊓(Q F t).map ι := by
    change (Q F β⊓Q F t).map ι=_
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQb]
  have hRne : R≠⊥ := by
    intro he
    apply hD
    have hh := hdec
    rw [he,sup_bot_eq] at hh
    rw [←hDm,hh]
  have hCE : C≤stabilizer F α⊓stabilizer F β :=
    le_inf (fun c hc => (hfix hc).1.1.1.2) (fun c hc => (hfix hc).1.1.2)
  have hCy : C≤stabilizer F y⊓stabilizer F u :=
    le_inf (fun c hc => (hfix hc).2) (fun c hc => (hfix hc).1.2)
  obtain ⟨hdy,hgy⟩ := CommutingTrivial.path_cartan_complement_at_edge H hab hy.symm C hCE hCy ho hd hgen
  have hRu : R≤Q F u := by rw [hfour]; exact inf_le_left.trans inf_le_right
  have hRS : R≤(stabilizer F y⊓stabilizer F u).pCoreIn 2 :=
    hRu.trans (by simpa only [inf_comm,reducedFamily] using graph_Q_le_edgeCore H hy)
  have hnR : C≤normalizer (R:Set (G₀ L S)) := fun c hc => (hn hc).1.2
  let eG (i : Bool) := (reduced_graphLinearQuotient h i (e i)).trans
    (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (K i)).symm
  have hyt : y.type=true := by
    have hu := hβu.1
    have hyy := hy.1
    change true≠u.type at hu
    cases hut : u.type <;> cases hyt : y.type
    · exact False.elim (hyy (hut.trans hyt.symm))
    · rfl
    · exact False.elim (hu hut.symm)
    · exact False.elim (hu hut.symm)
  have hmove : ⁅R,C⁆=R := cartan_separated_root_commutator H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hy.symm (source_linear_quotient_at H K eG y)
    (by simpa only [hyt] using hK) C R hCy hdy hgy ho hRS hnR hRne (disjoint_iff.mpr hzero)
  have hmovβ : ⁅R,C⊓graphLocalGroup F β⁆=R :=
    (commutator_eq_of_centralizing_sup hprod.symm (le_centralizer_iff.mp hRC)
      (inf_le_left.trans hnR)).trans hmove
  have hRcomm : R≤⁅Q F β,graphLocalGroup F β⁆ :=
    hmovβ.symm.le.trans (commutator_mono (inf_le_left.trans inf_le_left) inf_le_right)
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let L₁ := enlargedEndpoint L S 1
  have hRm : R.map ι= (Q₁⊓(Q F t).map ι)⊓
      centralizer (((Z F u).map ι⊔(Z F (g • u)).map ι:Subgroup G):Set G) := by
    change (D F β t⊓centralizer ((Z F u⊔Z F (g • u):Subgroup (G₀ L S)):Set (G₀ L S))).map ι=_
    rw [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,hDm,Subgroup.map_sup]
  have hspan : conjugateSpanBy (R.map ι) L₁=Q₁ := by
    rw [hRm]
    exact (original_bTwo_strict_residual_normal_generation h hc hne hb hβu ht htne hD g hg hgt).2
  have hRorig : R.map ι≤⁅Q₁,L₁⁆ := by
    have hh := map_mono (f:=ι) hRcomm
    rwa [map_commutator,hQb,reduced_graphLocalGroup_image h true] at hh
  have hnorm : L₁≤normalizer (Q₁:Set G) := by
    have hnQ : graphLocalGroup F β≤normalizer (Q F β:Set (G₀ L S)) :=
      (sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Q F β)
    have hh := (map_mono (f:=ι) hnQ).trans ((Q F β).le_normalizer_map ι)
    rwa [hQb,reduced_graphLocalGroup_image h true] at hh
  exact le_antisymm (le_normalizer_iff_commutator_le_left.mp hnorm)
    (hspan.symm.le.trans (conjugateSpanBy_le hRorig (normalizer_commutator_ge_right Q₁ L₁)))

/-- The same original beta enlargement has no nontrivial two-group quotient:
this is the source identity `O²(L_beta) = L_beta`. -/
theorem original_bTwo_nonbinary_beta_twoPerfect
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    pResidual 2 (enlargedEndpoint L S 1)=⊤ := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let M := graphLocalGroup F β
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hfour : 3<Nat.card (K true) := by
    let : Fintype (K true) := Fintype.ofFinite (K true)
    have heven : Even (Nat.card (K true)) := by
      rw [Nat.card_eq_fintype_card,even_iff_two_dvd]
      exact (CharP.cast_eq_zero_iff (K true) 2 _).mp (FiniteField.cast_card_eq_zero (K true))
    obtain ⟨n,hn⟩ := heven
    omega
  let : Group.IsPerfect PSL(2,K true) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three (K true) hfour
  let eQ := reduced_graphLinearQuotient h true (e true)
  let : Group.IsPerfect (M⧸pCore 2 M) := Group.IsPerfect.ofSurjective (f:=eQ.symm.toMonoidHom) eQ.symm.surjective
  have hco : ⁅Q F β,M⁆=Q F β := by
    apply Subgroup.map_injective (G₀ L S).subtype_injective
    rw [map_commutator,reduced_base_Q_map h true,reduced_graphLocalGroup_image h true]
    exact original_bTwo_nonbinary_beta_core_commutator h hc hne hb hβu ht htne K e hK hD
  have hcore : (pCore 2 M).map M.subtype=Q F β := CommutingTrivial.graphLocalGroup_core H β
  have hker : pCore 2 M≤_root_.commutator M := by
    apply (Subgroup.map_le_map_iff_of_injective M.subtype_injective).mp
    rw [hcore,map_subtype_commutator,←hco]
    exact commutator_mono (by rw [←hcore]; exact map_subtype_le _) le_rfl
  let q := QuotientGroup.mk' (pCore 2 M)
  have him : (_root_.commutator M).map q=⊤ := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact Group.IsPerfect.commutator_eq_top
  have htop : _root_.commutator M=⊤ := by
    have hh := congrArg (comap q) him
    rw [Subgroup.comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hker,Subgroup.comap_top] at hh
    exact hh
  let : Group.IsPerfect M := ⟨htop⟩
  let eM := (M.equivMapOfInjective ι (G₀ L S).subtype_injective).trans
    (MulEquiv.subgroupCongr (reduced_graphLocalGroup_image h true))
  let : Group.IsPerfect (enlargedEndpoint L S 1) := Group.IsPerfect.ofSurjective (f:=eM.toMonoidHom) eM.surjective
  let : Finite (enlargedEndpoint L S 1) := Finite.of_equiv M eM.toEquiv
  apply (pResidual_eq_top_iff 2 _).mpr
  intro N hN htwo
  let := hN
  by_contra hneN
  let : Nontrivial ((enlargedEndpoint L S 1)⧸N) := QuotientGroup.nontrivial_iff.mpr hneN
  let : Group.IsPerfect ((enlargedEndpoint L S 1)⧸N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent ((enlargedEndpoint L S 1)⧸N) := htwo.isNilpotent
  exact Group.IsPerfect.not_isSolvable ((enlargedEndpoint L S 1)⧸N) inferInstance

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
