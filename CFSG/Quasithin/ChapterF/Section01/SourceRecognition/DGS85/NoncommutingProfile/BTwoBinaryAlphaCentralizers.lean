module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoIntrinsicResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoResidualPairing
public import Theory.SpecificGroups.SL2.FieldCardinality

/-!
# Binary-alpha centralizers in the terminal separation argument

For a nonidentity element of the actual residual R_alpha, the faithful
commutator pairing with Q_alpha intersect Q_beta takes values in the
order-two beta center. Its centralizer therefore has index exactly two,
both in this intersection and in V_beta intersect Q_alpha. The opposite
center group is transitive at alpha and centralizes the residual element;
graph faithfulness rules out transitivity of its beta centralizer.

The derived subgroup of every beta-type core is its center layer of order
two. Consequently each element of such a core has centralizer index at
most two in its radius group. The two opposite radius/core factors at
the tested terminal intersection have full beta-root images. Restricting
them to the centralizer loses at most a factor of two in those images.
Their join lies in the literal original beta enlargement and remains
nontransitive on its neighbors.

All source applications construct the center actions internally and retain
one opposite-center lift, the original core denominators, and the actual
reduced-to-original inclusion. This supplies the two large centralizing
root images on p.161. The subsequent rank-one subgroup restriction and
field-four contradiction, hence nonbinary terminal separation itself,
remain to be proved.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.7)--(10.8), printed pp.159--161, especially the binary-alpha,
nonbinary-beta paragraph on p.161.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting

private theorem centralizer_index_dvd
    {G : Type*} [Group G] (A C : Subgroup G) [Finite C]
    (x : G) (hC : A ≤ centralizer (C : Set G))
    (hv : ∀ a ∈ A, ⁅x,a⁆ ∈ C) :
    (centralizer ({x}:Set G)).relIndex A ∣ Nat.card C := by
  let f : A →* C := {
    toFun := fun a => ⟨⁅x,(a:G)⁆,hv a a.property⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro a b
      apply Subtype.ext
      change ⁅x,(a:G)*(b:G)⁆=⁅x,(a:G)⁆*⁅x,(b:G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hc := hC a.property _ (hv b b.property)
      calc
        _ = ⁅x,(a:G)⁆*((a:G)*⁅x,(b:G)⁆)*(a:G)⁻¹ := by group
        _ = _ := by rw [←hc]; group }
  have hk : f.ker=(centralizer ({x}:Set G)).subgroupOf A := by
    ext a
    change (⟨⁅x,(a:G)⁆,hv a a.property⟩:C)=1 ↔ _
    rw [Subtype.ext_iff]
    change ⁅x,(a:G)⁆=1 ↔ (a:G)∈centralizer ({x}:Set G)
    rw [commutatorElement_eq_one_iff_mul_comm,mem_centralizer_singleton_iff]
    exact eq_comm
  change ((centralizer ({x}:Set G)).subgroupOf A).index ∣ Nat.card C
  rw [←hk,index_ker]
  exact f.range.card_subgroup_dvd_card

private theorem centralizer_index_two
    {G : Type*} [Group G] (A C : Subgroup G) [Finite C]
    (x : G) (hC : A ≤ centralizer (C : Set G))
    (hv : ∀ a ∈ A, ⁅x,a⁆ ∈ C) (hc : Nat.card C=2)
    (hx : x∉centralizer (A:Set G)) :
    (centralizer ({x}:Set G)).relIndex A=2 := by
  have hd := centralizer_index_dvd A C x hC hv
  rw [hc] at hd
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with hh|hh
  · apply (hx ?_).elim
    intro a ha
    exact mem_centralizer_singleton_iff.mp (relIndex_eq_one.mp hh ha)
  · exact hh

private theorem residual_centralizer_not_transitive
    {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B)=pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype≤B)
    {v m : Vertex (family P)} (hm : (graph (family P)).Adj v m)
    (W : Subgroup G) (hW : W⊔Q (family P) v=graphLocalGroup (family P) v)
    (x : G) (hxv : x∈Q (family P) v) (hxm : x∈Q (family P) m)
    (hxW : x∈centralizer (W:Set G)) (hx : x≠1) :
    ¬ ∀ z : Vertex (family P), (graph (family P)).Adj m z →
      ∃ a∈graphLocalGroup (family P) m⊓centralizer ({x}:Set G), a • v=z := by
  intro htrans
  let F := family P
  have hnorm : centralizer ({x}:Set G)≤normalizer (zpowers x:Set G) := by
    rw [←centralizer_closure,←zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hbot : zpowers x=⊥ := by
    apply CommutingNontrivial.source_normalized_edge_eq_bot h hm _
      (zpowers_le.mpr ⟨Q_le_stabilizer F v hxv,Q_le_stabilizer F m hxm⟩)
    · intro z hz
      obtain ⟨a,ha,haz⟩ := graphLocalGroup_transitive h hB hS v ⟨m,hm⟩ ⟨z,hz⟩
      change a • m=z at haz
      have hn : W≤normalizer (Q F v:Set G) :=
        (le_sup_left.trans hW.le).trans ((sylowGenerated_le _).trans
          (CommutingNontrivial.stabilizer_normalizes_Q F v))
      have hp : a∈(W:Set G)*(Q F v:Set G) := by
        rw [←coe_mul_of_left_le_normalizer_right W (Q F v) hn,hW]
        exact ha
      obtain ⟨w,hw,q,hq,rfl⟩ := hp
      have hqm : q • m=m := ((source_Z_Q_U h v).2.trans
        ((ballKernel_one_le_edge F hm).trans inf_le_right)) hq
      refine ⟨w,hnorm (mem_centralizer_singleton_iff.mpr (hxW w hw)),?_⟩
      simpa only [mul_smul,hqm] using haz
    · intro z hz
      obtain ⟨a,ha,haz⟩ := htrans z hz
      exact ⟨a,hnorm ha.2,haz⟩
  exact hx (mem_bot.mp (hbot ▸ mem_zpowers x))

private theorem half_index_bound
    {G : Type*} [Group G] (N A C : Subgroup G) [Finite A]
    (hC : C.relIndex A≤2) : N.relIndex A≤2*N.relIndex (A⊓C) := by
  have hh := relIndex_inf_mul_relIndex N C A
  have hle : N.relIndex A≤(N⊓C).relIndex A :=
    relIndex_le_of_le_left inf_le_left ((N⊓C).subgroupOf A).index_ne_zero_of_finite
  rw [←hh,inf_comm C A] at hle
  exact hle.trans (by simpa only [mul_comm] using
    Nat.mul_le_mul_left (N.relIndex (A⊓C)) hC)

private theorem opposite_radius_index
    {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B)=pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype≤B)
    {k W K : Type*} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Field K] [Finite K] [CharP K 2]
    {v m w t : Vertex (family P)} (hb : b (family P)=2)
    (c : BTwoCenterActionData (family P) v m w k W)
    (ht : (graph (family P)).Adj v t) (hne : t≠m)
    (hnot : ¬stabilizer (family P) v≤
      normalizer ((Q (family P) m⊓Q (family P) v:Subgroup G):Set G))
    (e : (graphLocalGroup (family P) m⧸pCore 2 (graphLocalGroup (family P) m))≃*SL(2,K)) :
    (Q (family P) m).relIndex (V (family P) t 1⊓Q (family P) v)=Nat.card K := by
  let F := family P
  let _ : ∀ i, Finite (F i) := finite_endpoints h
  have hSyl := source_kernel_sylow h hB hS
  have hi : (D F m t).relIndex (V F m 1⊓Q F v)=Nat.card K :=
    (c.seed_factor_index_eq h hSyl hb ht hne).symm.trans
      (c.linear_seed_factor_index h hB hS hSyl hb ht hne hnot e)
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  have hn := c.D_stabilizer_normalized h hSyl hb ht hne
  have hgv : (g:G) • v=v := c.actor_le g.property
  have hd : (D F m t).map (MulAut.conj (g:G)).toMonoidHom=D F m t :=
    mem_normalizer_iff_map_conj_eq.mp (hn (c.actor_le g.property))
  have htidx := relIndex_map_map_of_injective (f:=(MulAut.conj (g:G)).toMonoidHom)
    (D F m t) (V F m 1⊓Q F v) (MulAut.conj (g:G)).injective
  rw [hd,map_inf _ _ _ (MulAut.conj (g:G)).injective,←V_translate,←Q_translate,hg,hgv,hi] at htidx
  have hsub : (D F m t).subgroupOf (V F t 1⊓Q F v)=
      (Q F m).subgroupOf (V F t 1⊓Q F v) := by
    ext x
    change ((x:G)∈Q F m ∧ (x:G)∈Q F t) ↔ (x:G)∈Q F m
    exact ⟨And.left,fun hx => ⟨hx,
      graph_V_le_Q_of_short h hSyl t (by rw [hb]; decide) x.property.1⟩⟩
  change ((D F m t).subgroupOf (V F t 1⊓Q F v)).index=Nat.card K at htidx
  rw [hsub] at htidx
  exact htidx

namespace Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)
variable {K₀ K : Type*} [Field K₀] [Finite K₀] [CharP K₀ 2]
  [Field K] [Finite K] [CharP K 2]

private theorem alpha_field_card
    (h : HypothesisF11 L S) {u : Vertex F}
    {k : Type u} [Field k] [Finite k] [CharP k 2] [Algebra (ZMod 2) k]
    (c : BTwoCenterActionData F α β u k (Fin 2 → k))
    (hactor : c.actor=graphLocalGroup F α)
    (e₀ : (L 0⧸pCore 2 (L 0))≃*PSL(2,K₀)) : Nat.card k=Nat.card K₀ := by
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hc : pCore 2 c.actor=(Q F α).subgroupOf c.actor := by
    apply map_injective c.actor.subtype_injective
    rw [map_subgroupOf_eq_of_le c.core_le]
    change c.actor.pCoreIn 2=_
    rw [hactor]
    exact sylowGenerated_core (stabilizer F α)
  let ec : (c.actor⧸pCore 2 c.actor)≃*SL(2,k) :=
    (QuotientGroup.quotientMulEquivOfEq (hc.trans c.kernel.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective c.quotient c.onto)
  let ea : (c.actor⧸pCore 2 c.actor)≃*SL(2,K₀) := by
    rw [hactor]
    exact (reduced_graphLinearQuotient h false e₀).trans
      (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K₀)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  exact Matrix.SL2.field_card_eq_of_equiv (ec.symm.trans ea)

/-- Both radius/core factors used in the terminal argument have full
beta-root images, with the literal original beta core as denominator. -/
theorem original_bTwo_opposite_radius_indices
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (hy : (graph F).Adj u y) (hyne : y≠β)
    (e : (L 1⧸pCore 2 (L 1))≃*PSL(2,K)) :
    let Q₁ := (parabolic L S 1).pCoreIn 2
    Q₁.relIndex ((V F t 1).map ι⊓(parabolic L S 0).pCoreIn 2)=Nat.card K ∧
      Q₁.relIndex ((V F y 1).map ι⊓(Q F u).map ι)=Nat.card K := by
  obtain ⟨k₀,f₀,n₀,ch₀,a₀,k₁,f₁,n₁,ch₁,a₁,c₀,c₁,ha₀,ha₁,_,_,_⟩ :=
    reduced_bTwo_equal_field_profile_actions h hc hne hb
      (by exact ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩) hβu
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have h0 := opposite_radius_index (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb c₀ ht htne
    (reduced_graph_core_obstruction h α β c₀.middle) eβ
  have h1 := opposite_radius_index (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb c₁ hy hyne
    (reduced_graph_core_obstruction h u β c₁.middle) eβ
  have hQam : (Q F α).map ι=(parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  have hQbm : (Q F β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  constructor
  · rw [←hQam,←hQbm,←map_inf _ _ _ (G₀ L S).subtype_injective,
      relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
    exact h0
  · rw [←hQbm,←map_inf _ _ _ (G₀ L S).subtype_injective,
      relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
    exact h1

/-- Binary alpha gives exact adjacent-core centralizer indices and a
nontransitive beta centralizer for every nonidentity source residual element.
The radius groups at every beta-type vertex have centralizer index at most two
for elements of that vertex core, including both terminal radius groups. -/
theorem original_bTwo_alpha_binary_residual_centralizers
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (e₀ : (L 0⧸pCore 2 (L 0))≃*PSL(2,K₀)) (hK₀ : Nat.card K₀=2)
    (e : (L 1⧸pCore 2 (L 1))≃*PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    ∃ g∈graphLocalGroup F α, g • β=t ∧
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      let X₀ := (V F β 1).map ι⊓Q₀
      W₀⊔Q₀=enlargedEndpoint L S 0 ∧
      R₀=(D₀⊓(Q F u).map ι)⊓(Q F (g • u)).map ι ∧ R₀≠⊥ ∧
      (∀ x∈R₀, x≠1 →
        (centralizer ({x}:Set G)).relIndex (Q₀⊓Q₁)=2 ∧
        (centralizer ({x}:Set G)).relIndex X₀=2 ∧
        ¬∀ z : Vertex F, (graph F).Adj β z →
          ∃ a∈graphLocalGroup F β, ι a∈centralizer ({x}:Set G) ∧ a • α=z) ∧
      (∀ z : Vertex F, z.type=true → ∀ x∈(Q F z).map ι,
        (centralizer ({x}:Set G)).relIndex ((V F z 1).map ι)≤2) := by
  classical
  obtain ⟨k,f,fin,ch,alg,c,hactor,hkmin,n,hn,hm,hpow,g,hg,
    hgen,hfour,hwhole,hRne,hDel,hRel,hdec,hdis,hprod,hZ,hDcard,hQcard,hnP,hnB⟩ :=
    original_bTwo_strict_residual h hc hne hb hβu ht htne hD
  change BTwoCenterActionData F α β u k (Fin 2 → k) at c
  change c.actor=graphLocalGroup F α at hactor
  have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hk : Nat.card k=2 := (alpha_field_card h c hactor e₀).trans hK₀
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β := c.middle
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let D₀ := Q₁⊓(Q F t).map ι
  let Z₁ := (Z F β).map ι
  let I := Q₀⊓Q₁
  let X := (V F β 1).map ι⊓Q₀
  let W := Z F u⊔Z F ((g:G₀ L S) • u)
  let W₀ := (Z F u).map ι⊔(Z F ((g:G₀ L S) • u)).map ι
  let R := D₀⊓centralizer (W₀:Set G)
  have hQam : (Q F α).map ι=Q₀ := reduced_base_Q_map h false
  have hQbm : (Q F β).map ι=Q₁ := reduced_base_Q_map h true
  have hDm : (D F β t).map ι=D₀ := by
    change (Q F β⊓Q F t).map ι=_
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQbm]
  have hIm : (Q F α⊓Q F β).map ι=I := by
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQam,hQbm]
  have hXm : (V F β 1⊓Q F α).map ι=X := by
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQam]
  have hID : I=X⊔D₀ := by
    rw [←hIm,←hXm,←hDm,←Subgroup.map_sup]
    exact congrArg (map ι) (c.seed_adjacent_intersection H (reduced_kernel_sylow h) hb ht htne)
  have hder : ⁅Q₁,Q₁⁆=Z₁ := by
    have hh := congrArg (map ι) (c.beta_core_frattini_eq H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm).2
    change (⁅Q F β,Q F β⁆).map ι=Z₁ at hh
    rwa [map_commutator,hQbm] at hh
  have hZcard : Nat.card Z₁=2 := by
    rw [show Z₁=(Z F β).map ι from rfl,card_map_of_injective (G₀ L S).subtype_injective]
    exact (c.central_middle_center_card H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral (LinearEquiv.refl _ _)).trans hk
  have hQC : Q₁≤centralizer (Z₁:Set G) := by
    have hh := (map_mono (f:=ι) (graph_Q_centralizes_Z H β)).trans
      (map_centralizer_le_centralizer_image _ _)
    change (Q F β).map ι≤centralizer (Z₁:Set G) at hh
    rw [hQbm] at hh
    exact hh
  have hXQ : X≤Q₁ := by
    rw [←hXm,←hQbm]
    exact map_mono (inf_le_left.trans (graph_V_le_Q_of_short H (reduced_kernel_sylow h)
      β (by change 1 < b F; rw [hb]; decide)))
  let : Finite Z₁ := Nat.finite_of_card_ne_zero (by rw [hZcard]; decide)
  let := hDel
  have hRD : R≤centralizer (D₀:Set G) :=
    inf_le_left.trans (le_centralizer D₀)
  have hfaith := Assembly.BTwoSource.original_bTwo_residual_endpoint_centralizer
    h hc hne hb hβu ht htne c hactor eβ g hg hgen hDel
  have hW : W⊔Q F α=graphLocalGroup F α := by
    apply map_injective (G₀ L S).subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,hQam,reduced_graphLocalGroup_image h false]
    exact hgen
  refine ⟨g,hactor ▸ g.property,hg,hgen,hfour,hRne,?_,?_⟩
  · intro x hx hx1
    have hxI : x∉centralizer (I:Set G) := fun hh =>
      hx1 (mem_bot.mp (hfaith ▸ ⟨hx,hh⟩))
    have hxX : x∉centralizer (X:Set G) := by
      intro hh
      apply hxI
      have hc : X⊔D₀≤centralizer ({x}:Set G) := sup_le
        (fun z hz => mem_centralizer_singleton_iff.mpr (hh z hz))
        (fun z hz => mem_centralizer_singleton_iff.mpr (hRD hx z hz))
      intro z hz
      exact mem_centralizer_singleton_iff.mp (hc (hID ▸ hz))
    refine ⟨centralizer_index_two I Z₁ x (inf_le_right.trans hQC)
      (fun a ha => hder ▸ commutator_mem_commutator hx.1.1 ha.2) hZcard hxI,
      centralizer_index_two X Z₁ x (hXQ.trans hQC)
        (fun a ha => hder ▸ commutator_mem_commutator hx.1.1 (hXQ ha)) hZcard hxX,?_⟩
    obtain ⟨r,hr,rfl⟩ := show x∈(Q F β).map ι from hQbm.symm ▸ hx.1.1
    have hrQ : r∈Q F α := by
      have hRα : R≤Q₀ := by
        change D₀⊓centralizer (W₀:Set G)≤Q₀
        rw [←hDm,←hQam]
        obtain ⟨_,_,hDQ,_⟩ := c.central_D_structure H (reduced_kernel_sylow h) hb
          (c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
            (reduced_vertex_sylow h) hactor hcentral) ht htne
        exact inf_le_left.trans (map_mono hDQ)
      have hh := hRα hx
      rw [←hQam] at hh
      obtain ⟨r',hr',he⟩ := hh
      exact (G₀ L S).subtype_injective he ▸ hr'
    have hrW : r∈centralizer (W:Set (G₀ L S)) := by
      intro w hw
      apply (G₀ L S).subtype_injective
      change ι (w*r)=ι (r*w)
      rw [map_mul,map_mul]
      apply hx.2
      change ι w∈(Z F u).map ι⊔(Z F ((g:G₀ L S) • u)).map ι
      rw [←Subgroup.map_sup]
      exact mem_map_of_mem ι hw
    have hr1 : r≠1 := fun hh => hx1 (by rw [hh,map_one])
    intro htrans
    apply residual_centralizer_not_transitive H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hab W hW r hrQ hr hrW hr1
    intro z hz
    obtain ⟨a,ha,hac,haz⟩ := htrans z hz
    refine ⟨a,⟨ha,mem_centralizer_singleton_iff.mpr ?_⟩,haz⟩
    apply (G₀ L S).subtype_injective
    change ι (a*r)=ι (r*a)
    rw [map_mul,map_mul]
    exact mem_centralizer_singleton_iff.mp hac
  · intro z hz x hx
    obtain ⟨a,ha⟩ := Subgroup.CosetGeometry.exists_smul_base F z
    have haz : a • β=z := by simpa only [hz] using ha
    have hZz : Nat.card ((Z F z).map ι)=2 := by
      rw [←haz,Z_translate,map_map]
      rw [←map_map,card_map_of_injective (G₀ L S).subtype_injective,
        card_map_of_injective (MulAut.conj a).injective]
      rw [←card_map_of_injective (f:=ι) (G₀ L S).subtype_injective]
      exact hZcard
    have hdz : ⁅(Q F z).map ι,(Q F z).map ι⁆=(Z F z).map ι := by
      rw [←map_commutator]
      have hdb := (c.beta_core_frattini_eq H (reduced_borel_core_sylow h)
        (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm).2
      change ⁅Q F β,Q F β⁆=Z F β at hdb
      rw [←haz,Q_translate,Z_translate,←map_commutator,hdb]
    have hVz : (V F z 1).map ι≤(Q F z).map ι := map_mono
      (graph_V_le_Q_of_short H (reduced_kernel_sylow h) z (by change 1 < b F; rw [hb]; decide))
    have hcz : (Q F z).map ι≤centralizer ((Z F z).map ι:Set G) :=
      (map_mono (graph_Q_centralizes_Z H z)).trans (map_centralizer_le_centralizer_image _ _)
    let : Finite ((Z F z).map ι) := Nat.finite_of_card_ne_zero (by rw [hZz]; decide)
    have hd := centralizer_index_dvd ((V F z 1).map ι) ((Z F z).map ι) x
      (hVz.trans hcz) (fun a ha => hdz ▸ commutator_mem_commutator hx (hVz ha))
    rw [hZz] at hd
    exact Nat.le_of_dvd (by decide) hd

/-- The contrary terminal intersection supplies the two large centralizing
root images used on DGS p.161. Their generated subgroup lies in the actual
beta enlargement and cannot be transitive on the beta neighbors. -/
theorem original_bTwo_alpha_binary_terminal_half_roots
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (e₀ : (L 0⧸pCore 2 (L 0))≃*PSL(2,K₀)) (hK₀ : Nat.card K₀=2)
    (e : (L 1⧸pCore 2 (L 1))≃*PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    ∃ g∈graphLocalGroup F α, g • β=t ∧
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      W₀⊔Q₀=enlargedEndpoint L S 0 ∧
      R₀=(D₀⊓(Q F u).map ι)⊓(Q F (g • u)).map ι ∧ R₀≠⊥ ∧
      ∀ y : Vertex F, (graph F).Adj u y → y≠β →
        ∀ x∈R₀⊓(Q F y).map ι, x≠1 →
          let C₀ := ((V F t 1).map ι⊓Q₀)⊓centralizer ({x}:Set G)
          let C₁ := ((V F y 1).map ι⊓(Q F u).map ι)⊓centralizer ({x}:Set G)
          Nat.card K≤2*Q₁.relIndex C₀ ∧ Nat.card K≤2*Q₁.relIndex C₁ ∧
          C₀⊔C₁≤enlargedEndpoint L S 1⊓centralizer ({x}:Set G) ∧
          ¬∀ z : Vertex F, (graph F).Adj β z →
            ∃ a∈graphLocalGroup F β, ι a∈C₀⊔C₁ ∧ a • α=z := by
  obtain ⟨g,hg,hgt,hW,hfour,hRne,hrows,hsmall⟩ :=
    original_bTwo_alpha_binary_residual_centralizers h hc hne hb hβu ht htne e₀ hK₀ e hD
  refine ⟨g,hg,hgt,hW,hfour,hRne,?_⟩
  intro y hy hyne x hx hx1
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let A := (V F t 1).map ι⊓(parabolic L S 0).pCoreIn 2
  let B := (V F y 1).map ι⊓(Q F u).map ι
  let C := centralizer ({x}:Set G)
  let Q₁ := (parabolic L S 1).pCoreIn 2
  have htType : t.type=true := by
    have hh := ht.1
    change false≠t.type at hh
    cases hty : t.type <;> simp_all
  have huType : u.type=false := by
    have hh := hβu.1
    change true≠u.type at hh
    cases huy : u.type <;> simp_all
  have hyType : y.type=true := by
    have hh := hy.1
    rw [huType] at hh
    cases hyy : y.type <;> simp_all
  have hVfinite (z : Vertex F) : Finite ((V F z 1).map ι) := by
    have hV : V F z 1≤stabilizer F z :=
      (graph_V_le_Q_of_short H (reduced_kernel_sylow h) z
        (by change 1 < b F; rw [hb]; decide)).trans (Q_le_stabilizer F z)
    let : Finite (V F z 1) := Finite.of_injective (inclusion hV) (inclusion_injective _)
    exact Finite.of_equiv (V F z 1)
      ((V F z 1).equivMapOfInjective ι (G₀ L S).subtype_injective).toEquiv
  let : Finite ((V F t 1).map ι) := hVfinite t
  let : Finite ((V F y 1).map ι) := hVfinite y
  let : Finite A := Finite.of_injective (inclusion (show A≤(V F t 1).map ι from inf_le_left)) (inclusion_injective _)
  let : Finite B := Finite.of_injective (inclusion (show B≤(V F y 1).map ι from inf_le_left)) (inclusion_injective _)
  have hct : C.relIndex A≤2 :=
    (relIndex_le_of_le_right inf_le_left
      (C.subgroupOf ((V F t 1).map ι)).index_ne_zero_of_finite).trans
      (hsmall t htType x hx.1.1.2)
  have hcy : C.relIndex B≤2 :=
    (relIndex_le_of_le_right inf_le_left
      (C.subgroupOf ((V F y 1).map ι)).index_ne_zero_of_finite).trans
      (hsmall y hyType x hx.2)
  obtain ⟨hAi,hBi⟩ := original_bTwo_opposite_radius_indices h hc hne hb hβu ht htne hy hyne e
  have hAL : A≤enlargedEndpoint L S 1 := by
    have hab : (graph F).Adj α β :=
      ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
    have hQa : Q F α≤graphLocalGroup F β := pGroup_le_sylowGenerated _ _
      ((source_Z_Q_U H α).2.trans ((ballKernel_one_le_edge F hab).trans inf_le_right))
      (isPGroup_pCoreIn 2 _)
    have hh := map_mono (f:=ι) hQa
    rw [reduced_base_Q_map h false,reduced_graphLocalGroup_image h true] at hh
    exact inf_le_right.trans hh
  have hBL : B≤enlargedEndpoint L S 1 := by
    have hQu : Q F u≤graphLocalGroup F β := pGroup_le_sylowGenerated _ _
      ((source_Z_Q_U H u).2.trans ((ballKernel_one_le_edge F hβu.symm).trans inf_le_right))
      (isPGroup_pCoreIn 2 _)
    have hh := map_mono (f:=ι) hQu
    rw [reduced_graphLocalGroup_image h true] at hh
    exact inf_le_right.trans hh
  have hspan : (A⊓C)⊔(B⊓C)≤enlargedEndpoint L S 1⊓C :=
    sup_le (le_inf (inf_le_left.trans hAL) inf_le_right)
      (le_inf (inf_le_left.trans hBL) inf_le_right)
  refine ⟨?_,?_,hspan,?_⟩
  · change Nat.card K≤2*Q₁.relIndex (A⊓C)
    rw [←hAi]
    exact half_index_bound Q₁ A C hct
  · change Nat.card K≤2*Q₁.relIndex (B⊓C)
    rw [←hBi]
    exact half_index_bound Q₁ B C hcy
  · intro htrans
    apply (hrows x hx.1 hx1).2.2
    intro z hz
    obtain ⟨a,ha,hac,haz⟩ := htrans z hz
    exact ⟨a,ha,(hspan hac).2,haz⟩

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
