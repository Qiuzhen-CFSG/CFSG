module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryCartanKernels
public import Theory.SpecificGroups.SL2.OddSylowCentralizer

/-!
# Separation of the elementary local tori and the alpha Cartan kernel

An involutive alpha turn sends the beta center outside the original beta
core: mutual containment would make the two beta centers span the critical
alpha center inside that core. A full-Cartan reflection inverts its alpha
torus. An element in both local tori therefore centralizes both beta centers.
In the literal beta SL2 quotient an odd element cannot centralize the
nontrivial two-element supplied by the remote center. The local tori are
thus disjoint, with every relative subgroup and quotient map retained.

Apply this to the Cartan and reflections constructed from the original
nonbinary elementary source. If its full alpha permutation-kernel factor
were trivial, the proved Cartan factorization would put the entire Cartan
in the alpha actor. Torus separation would then kill the beta torus, whose
order is q_beta minus one. This forces the excluded binary beta quotient.
Thus the alpha Cartan-kernel condition in (14.5)(c) is now discharged.

ElementarySourceExchange supplies the actual exchange and marked U4
applications. The quotient Borel root signs, binary reflection choices,
nonelementary exclusions and complete 11.7/11.8 assembly remain distinct
source obligations.
Source: DGS, Groups and Graphs (1985), (11.6), pp.172--174;
(14.2)--(14.3), pp.210--212, and (14.6), pp.213--214.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The involutive alpha turn has a beta center escaping the opposite core. -/
theorem source_involutive_alpha_center_escape
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B)=pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P)=1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆=⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a≠c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (g : G) (hga : g∈stabilizer (family P) a) (hgb : g • b≠b) (hg2 : g*g=1) :
    ¬ Z (family P) (g • b) ≤ Q (family P) b := by
  let _ := finite_endpoints h
  intro hback
  have hgInv : g⁻¹=g := inv_eq_of_mul_eq_one_right hg2
  have hforward := map_mono (f := (MulAut.conj g).toMonoidHom) hback
  rw [←Z_translate,←Q_translate,smul_smul,hg2,one_smul] at hforward
  have hs := source_linear_rankOne_center_pair_span_of_mutual h hB d hc hb hcomm
    hbc hac Ma Mb ea g hga hgb hforward hback
  apply hc.2
  rw [hs]
  exact (sup_le ((source_Z_Q_U h b).1.trans (map_subtype_le _)) hback).trans (source_Z_Q_U h b).2

/-- The intersection of the local odd tori is trivial, using the source
reflection and the two actual beta centers as in DGS (14.6). -/
theorem source_elementary_local_tori_disjoint
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B)=pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P)=1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆=⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a≠c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    {k l : Type*} [Field k] [Finite k] [CharP k 2]
    [Field l] [Finite l] [CharP l 2]
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (graphLocalGroup (family P) b ⧸ pCore 2 (graphLocalGroup (family P) b)) ≃* SL(2,l))
    (hlocal : d.localGroup a=graphLocalGroup (family P) a)
    (hk : 2<Nat.card k)
    (C : Subgroup G) (hCE : C≤stabilizer (family P) a ⊓ stabilizer (family P) b)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2))
    (hgen : C ⊔ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      stabilizer (family P) a ⊓ stabilizer (family P) b)
    (hcentral : Q (family P) a ⊓ centralizer (C : Set G)=⊥)
    (g : G) (hg : g∈graphLocalGroup (family P) a)
    (hgn : g∈normalizer (C : Set G)) (hg2 : g*g=1) (hgb : g • b≠b) :
    Disjoint (C ⊓ graphLocalGroup (family P) a) (C ⊓ graphLocalGroup (family P) b) := by
  let _ := finite_endpoints h
  let Γ := family P
  let ea₀ : (graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃* SL(2,k) := by
    rw [←hlocal]
    exact ea
  have hab := source_critical_one_adjacent hc hb
  have hga : g∈stabilizer Γ a := sylowGenerated_le _ hg
  have hZb := (source_commuting_one_center_identities h hB hS hc hb hcomm).1
  have hZa : Z Γ b ≤ Z Γ a := source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hab.symm
  have hZga : Z Γ (g • b) ≤ Z Γ a := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hZa
    rwa [←Z_translate,←Z_translate,show g • a=a from hga] at hh
  have hZL : Z Γ (g • b) ≤ graphLocalGroup Γ b := by
    apply pGroup_le_sylowGenerated _ _ (hZga.trans ?_) (source_center_elementary h (g • b)).isPGroup
    exact (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      (source_Z_Q_U h a).2).trans ((ballKernel_one_le_edge Γ hab).trans inf_le_right)
  have hesc := source_involutive_alpha_center_escape h hB d hc hb hcomm hbc hac Ma Mb ea g hga hgb hg2
  obtain ⟨z,hz,hzQ⟩ : ∃ z, z∈Z Γ (g • b) ∧ z∉Q Γ b := by
    simpa only [SetLike.le_def,not_forall,Classical.not_imp,exists_prop] using hesc
  let H := graphLocalGroup Γ b
  let q := eb.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hker : q.ker=pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ eb.injective,QuotientGroup.ker_mk']
  let zz : H := ⟨z,hZL hz⟩
  have hzq : q zz≠1 := by
    intro he
    have hh : zz∈pCore 2 H := hker ▸ he
    exact hzQ ((CommutingTrivial.graphLocalGroup_core h b).le (mem_map_of_mem H.subtype hh))
  obtain ⟨R,hR⟩ := (((source_center_elementary h (g • b)).isPGroup.comap_subtype
    (K := H)).map q).exists_le_sylow
  apply disjoint_def.mpr
  intro x hx hy
  have hx2 : (g*x)*(g*x)=1 := ApartmentExchange.full_cartan_neighbor_transporter_square h hB hS hab ea₀ hk C
    hCE ho hd hgen hcentral (g*x) ((graphLocalGroup Γ a).mul_mem hg hx.2)
    ((normalizer (C : Set G)).mul_mem hgn (C.le_normalizer hx.1))
    (by simpa only [mul_smul,show x • b=b from (hCE hx.1).2] using hgb)
  have hinv : g*x*g⁻¹=x⁻¹ := by
    have hgi : g⁻¹=g := inv_eq_of_mul_eq_one_right hg2
    apply mul_right_cancel (b := x)
    rw [inv_mul_cancel,hgi]
    simpa only [mul_assoc] using hx2
  have hxc : x∈centralizer (Z Γ b : Set G) := by
    apply mem_centralizer_iff.mpr
    intro y hyZ
    exact ((mem_omegaCenterIn_iff _ _).mp (hZb ▸ hyZ)).2.1 x hy.2 |>.symm
  have hremote : x∈centralizer (Z Γ (g • b) : Set G) := by
    have hh := (centralizer (Z Γ b : Set G)).inv_mem hxc
    have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom hh
    have hm := map_centralizer_le_centralizer_image (Z Γ b : Set G) (MulAut.conj g).toMonoidHom hm
    change g*x⁻¹*g⁻¹ ∈ centralizer ((Z Γ b).map (MulAut.conj g).toMonoidHom : Set G) at hm
    rw [←Z_translate] at hm
    have hgInv : g⁻¹=g := inv_eq_of_mul_eq_one_right hg2
    have he : g*x⁻¹*g⁻¹=x := by
      have hh := congrArg Inv.inv hinv
      simpa only [mul_inv_rev,inv_inv,mul_assoc] using hh
    exact he ▸ hm
  let xx : H := ⟨x,hy.2⟩
  have hodd : Odd (orderOf xx) := by
    simpa only [xx,Subgroup.orderOf_mk] using ho.of_dvd_nat (orderOf_dvd_natCard (⟨x,hx.1⟩ : C))
  have hxq : q xx=1 := by
    by_contra hn
    apply hzq
    apply Matrix.SpecialLinearGroup.eq_one_of_sylow_commutes_nontrivial_odd R (q zz) (q xx)
      (hR (mem_map_of_mem q hz)) hn hodd (by rw [←map_pow,pow_orderOf_eq_one,map_one])
    apply Commute.map
    exact Subtype.ext (mem_centralizer_iff.mp hremote z hz)
  have hxQ : x∈Q Γ b := (CommutingTrivial.graphLocalGroup_core h b).le
    (mem_map_of_mem H.subtype (show xx∈pCore 2 H from hker ▸ hxq))
  exact disjoint_def.mp hd hx.1 ((Noncommuting.graph_Q_le_edgeCore h hab.symm).trans
    (by rw [inf_comm]) hxQ)
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))

include h hc hb hcomm helem


variable (c : CompatibleCartans L (reducedSylow L S))
    (t : Bool → (reducedAmalgam L S).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (htsq : ∀ i, t i*t i=1)
    (htnorm : ∀ i, t i∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))

include c t htfix htmove htsq htnorm

variable {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=8)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c t))
include hp hl hT


omit hp in
/-- The two local Cartan tori on a supported elementary alpha--beta edge
are disjoint. The reflection, center escape and quotient actions are supplied
by the original source, with no Cartan-kernel premise. -/
theorem original_elementary_nonbinary_adjacent_tori_disjoint
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hv : ((bOne_tree_cover h).vertex (p.getVert 4)).type=false) :
    let C := (cartan c).map (bOne_tree_map h)
    Disjoint (C ⊓ graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)))
      (C ⊓ graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 5))) := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let v := cov.vertex (p.getVert 4)
  let w := cov.vertex (p.getVert 5)
  let C := (cartan c).map φ
  let d := reducedFullEarlierLocalTheorems h
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ := cartan_abelian h c
  let _ : IsMulCommutative C := inferInstance
  change v.type=false at hv
  dsimp only
  have hvw : (graph F).Adj v w := cov.hom.map_adj (p.adj_getVert_succ (by omega))
  have hw : w.type=true := by
    have hh := hvw.1
    change v.type≠w.type at hh
    cases he : w.type
    · exact (hh (hv.trans he.symm)).elim
    · rfl
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,_⟩ :=
    original_elementary_apartment_actor_quotients h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
  have hfour : 2<Nat.card (K v.type) := by
    rw [hK,hv]
    simp only [Bool.false_eq_true,ite_false]
    have hh : 2^2≤2^(2*m) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨y,hyv,hyw⟩ := incident_common_translate F hvw.2
  rw [hv] at hyv
  rw [hw] at hyw
  have hcvw : IsCriticalPair F v w := by
    simpa only [hyv,hyw] using criticalPair_translate F hc y
  have hcommvw : ⁅Z F v,Z F w⁆=⊥ := by
    have hh := commuting_centers_translate F (base F false) (base F true) y
    rwa [hyv,hyw,hcomm,Subgroup.map_bot] at hh
  have M (z : Vertex F) : IsRankOneModel (d.localGroup z ⧸ pCore 2 (d.localGroup z)) := by
    apply IsRankOneModel.linear (if z.type then m else 2*m) (by split <;> omega)
    refine ⟨K z.type,inferInstance,inferInstance,hK z.type,?_⟩
    exact ⟨(e z).trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL : SL(2,K z.type) ≃* PSL(2,K z.type))⟩
  have hCE : C ≤ stabilizer F v ⊓ stabilizer F w := by
    rintro _ ⟨x,hx,rfl⟩
    constructor
    · change φ x • cov.vertex (p.getVert 4)=_
      rw [←cov.vertex_smul,reflectionApartment_fixed c t htnorm x hx _
        (hT _ (p.getVert_mem_support 4))]
    · change φ x • cov.vertex (p.getVert 5)=_
      rw [←cov.vertex_smul,reflectionApartment_fixed c t htnorm x hx _
        (hT _ (p.getVert_mem_support 5))]
  let E := F false ⊓ F true
  let W := (twoGroup L S).map φ
  have hmapE : (originalMiddle A).map φ=E := by
    rw [show originalMiddle A=T false ⊓ T true from
      (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
        (inclusion_injective (commonBorel_le_parabolic 1))).symm]
    exact cov.map_inf
  have hC0 : C ≤ E := hmapE ▸ map_mono (cartan_le c)
  have hW0 : W ≤ E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hWn : E ≤ normalizer (W : Set G₀) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hWcore : W ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hW0 hWn
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  let _ : Finite E := Finite.of_injective (inclusion (show E ≤ F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  have hd0 : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨r,hr⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact ho.coprime_two_right.pow_right r)
  have hg0 : C ⊔ E.pCoreIn 2=E := by
    apply le_antisymm (sup_le hC0 (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    exact he.symm.le.trans (sup_le (hWcore.trans le_sup_right) le_sup_left)
  have hEbase : E=stabilizer F (base F false) ⊓ stabilizer F (base F true) := by
    rw [show stabilizer F (base F false)=F false from Subgroup.CosetGeometry.stabilizer_base F false,
      show stabilizer F (base F true)=F true from Subgroup.CosetGeometry.stabilizer_base F true]
  have hbase : (graph F).Adj (base F false) (base F true) :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨hd,hg⟩ := CommutingTrivial.path_cartan_complement_at_edge (reduced_triple h)
    hbase hvw C (hEbase ▸ hC0) hCE ho (hEbase ▸ hd0) (hEbase ▸ hg0)
  have hfixed : Q F v ⊓ centralizer (C : Set G₀)=⊥ :=
    original_elementary_nonbinary_cartan_core_centralizer h hc hb hcomm helem hnb
      hvw C hCE ho hd hg
  obtain ⟨g,hgJ,hgn,hg2,hgv,hgw⟩ := original_elementary_nonbinary_cartan_reflection
    h hc hb hcomm helem hnb hvw C hCE ho hd hg
  have hcard : 1 < ((graph F).neighborSet w).ncard := by
    rw [←Nat.card_coe_set_eq,card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    have hh : 3 ≤ ((F (!w.type)).subgroupOf (F w.type)).index :=
      source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) w.type
    omega
  obtain ⟨z,hz,hzv⟩ := Set.exists_ne_of_one_lt_ncard hcard v
  exact source_elementary_local_tori_disjoint (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) d hcvw hb hcommvw
    hz hzv.symm (M v) (M w) (e v) (e w) rfl hfour C hCE ho hd hg hfixed
    g hgJ hgn hg2 hgw

/-- The nonbinary elementary source discharges the alpha Cartan-kernel
condition in DGS (14.5)(c). The full kernel G_alpha^(1) is retained. -/
theorem original_elementary_nonbinary_alpha_cartan_kernel_ne_bot
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hv : ((bOne_tree_cover h).vertex (p.getVert 4)).type=false) :
    (cartan c).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥ := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let v := cov.vertex (p.getVert 4)
  let w := cov.vertex (p.getVert 5)
  let C₀ := (cartan c).map φ
  let D := halfPathActor (X := (A).Universal) p 4
  have hfix : cartan c ≤ MulAction.stabilizer (A).Universal (p.getVert 4) := by
    intro k hk
    exact reflectionApartment_fixed c t htnorm k hk _ (hT _ (p.getVert_mem_support 4))
  have hφC (x : (A).Universal) (hx : x∈cartan c) (he : φ x=1) : x=1 := by
    have hh := cov.stabilizerEquiv (p.getVert 4) |>.injective
      (a₁ := ⟨x,hfix hx⟩) (a₂ := 1) (Subtype.ext (by change φ x=φ 1; simpa only [map_one] using he))
    exact congrArg Subtype.val hh
  intro hzero
  have hzero' : cartan c ⊓ (U F v).comap φ=⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply hφC x hx.1
    exact mem_bot.mp (hzero ▸ ⟨mem_map_of_mem φ hx.1,hx.2⟩)
  have hCD : cartan c ≤ D := by
    have hf := original_elementary_cartan_kernel_factorization h hc hb hcomm helem
      c t htfix htmove htsq htnorm p hp hl hT
    rw [hzero',sup_bot_eq] at hf
    exact hf.le.trans inf_le_right
  have hC0J : C₀ ≤ graphLocalGroup F v :=
    (map_mono hCD).trans (halfPathActor_map_le_local h p 4 hl)
  have hdis := original_elementary_nonbinary_adjacent_tori_disjoint h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hl hT hnb hv
  change Disjoint (C₀ ⊓ graphLocalGroup F v) (C₀ ⊓ graphLocalGroup F w) at hdis
  rw [inf_eq_left.mpr hC0J] at hdis
  have hCb : C₀ ⊓ graphLocalGroup F w=⊥ := by
    apply bot_unique
    intro x hx
    exact disjoint_def.mp hdis hx.1 hx
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,_⟩ :=
    original_elementary_apartment_actor_quotients h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
  have hw : w.type=true := by
    have hh := (cov.hom.map_adj (p.adj_getVert_succ (show 4<p.length by omega))).1
    change v.type≠w.type at hh
    change v.type=false at hv
    cases he : w.type
    · exact (hh (hv.trans he.symm)).elim
    · rfl
  have hc1 := (original_elementary_adjacent_cartan_orders h c t htnorm p hl hT (e v) (e w)).2
  change Nat.card (C₀ ⊓ graphLocalGroup F w : Subgroup G₀)=Nat.card (K w.type)-1 at hc1
  simp only [hCb,Subgroup.card_bot,hK,hw,ite_true] at hc1
  have hm1 : m=1 := by
    by_contra hn
    have hh : 2^2≤2^m := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  apply hnb
  let J₀ := graphLocalGroup F (base F true)
  let j := J₀.equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  refine ⟨K true,inferInstance,inferInstance,?_,?_⟩
  · simpa only [hm1,ite_true,Nat.pow_one] using hK true
  · exact ⟨(QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).symm.trans
      ((e (base F true)).trans
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL : SL(2,K true) ≃* PSL(2,K true)))⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
