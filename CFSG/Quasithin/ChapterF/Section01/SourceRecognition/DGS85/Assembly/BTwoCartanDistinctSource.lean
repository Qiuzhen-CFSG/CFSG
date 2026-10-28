module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoRegular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanDistinct
public import Theory.SpecificGroups.SL2.CoreTorusMover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicEdgeGeneration

/-!
# Distinct source Cartan factors in the nonsolvable distance-two branch

The adjacent odd local factors are disjoint by the natural center action.
If the alpha factor agreed with its beta-mover conjugate, the mover would
centralize it. Full-torus rigidity then makes that factor act trivially on
the beta quotient. Conjugating by the alpha mover places its commutators
with the alpha core in the neighboring-core intersection, contradicting
the fixed-point-free odd action on the natural alpha-core quotient.

Thus the two alpha factors are distinct and their join meets the beta
factor nontrivially. The final application constructs the same full path
Cartan and both movers directly from the original F.1.11 hypotheses.
Source: DGS, Groups and Graphs (1985), (10.7)--(10.8), printed pp.158--161.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Noncommuting NoncommutingProfile
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

theorem bTwo_odd_local_tori_disjoint
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v m w : Vertex F} (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (hZne : Z F m ≠ ⊥)
    (K : Subgroup G) (ho : Odd (Nat.card K)) :
    Disjoint (K ⊓ graphLocalGroup F v) (K ⊓ graphLocalGroup F m) := by
  let _ := finite_endpoints h
  let _ : Finite (Q F v) := Finite.of_injective
    (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)
  let _ : Finite (Z F v) := Finite.of_injective
    (inclusion (Z_le_stabilizer F v)) (inclusion_injective _)
  let _ : Finite W := Finite.of_surjective (fun z => (c.coordinates.coordinates z).toAdd)
    (fun x => c.coordinates.onto (Multiplicative.ofAdd x))
  have hω := c.omega_eq_bot_of_central_neighbor h hB hS hactor hcentral
  have hZm : Z F m ≤ Z F v := center_le_of_central_neighbor h hB hS c.middle hcentral
  obtain ⟨z,hz,hz1⟩ := (Z F m).bot_or_exists_ne_one.resolve_left hZne
  have hp : IsPGroup 2 (Q F v) := isPGroup_pCoreIn 2 (stabilizer F v)
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hdQ : Disjoint K (Q F v) := disjoint_of_coprime_natCard (by
    rw [hn]; exact ho.coprime_two_right.pow_right n)
  apply disjoint_def.mpr
  intro a ha ham
  let a' : c.actor := ⟨a,hactor.symm ▸ ha.2⟩
  by_contra ha1
  have hqa : c.quotient a' ≠ 1 := by
    intro he
    have hk : a' ∈ c.quotient.ker := he
    rw [c.kernel] at hk
    exact ha1 (disjoint_def.mp hdQ ha.1 hk)
  have hao : Odd (orderOf a') := by
    simpa only [a',Subgroup.orderOf_mk] using
      ho.of_dvd_nat (_root_.orderOf_dvd_natCard (⟨a,ha.1⟩ : K))
  have hfixed := odd_fixed_eq_bot_of_natural_copies c.representation
    (sl2_natural_copies c.representation c.imageSylow c.quadratic c.generated c.fixed_bot)
    (c.quotient a') hao (by rw [←map_pow,pow_orderOf_eq_one,map_one]) hqa
  let z' : Z F v := ⟨z,hZm hz⟩
  have hfix : (c.coordinates.coordinates z').toAdd ∈
      fixedSpace c.representation (zpowers (c.quotient a')) := by
    apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
    apply (c.coordinates.fixed_coordinate_iff_commutator_mem a' z').mpr
    have hzcomm : Commute z a := ((hcentral hz).2 a ham.2).symm
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hzcomm.eq]
    exact one_mem _
  have hz0 : (c.coordinates.coordinates z').toAdd = 0 := by
    simpa only [hfixed,Submodule.mem_bot] using hfix
  have hzk := (c.coordinates.coordinates_eq_one_iff z').mp
    (Multiplicative.toAdd.injective hz0)
  exact hz1 (by simpa only [hω,mem_bot] using hzk)

/-- A nontrivial odd subgroup of the alpha actor moves its natural core quotient. -/
theorem bTwo_odd_subgroup_moves_core_quotient
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (htne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    {J : Type*} [Field J] [Finite J] [CharP J 2]
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,J))
    (K : Subgroup G) (hKL : K ≤ c.actor) (ho : Odd (Nat.card K)) (hne : K ≠ ⊥) :
    ¬ ⁅Q F v,K⁆ ≤ D F m t := by
  let _ := finite_endpoints h
  let _ : Finite (Q F v) := Finite.of_injective
    (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)
  have hp : IsPGroup 2 (Q F v) := isPGroup_pCoreIn 2 (stabilizer F v)
  obtain ⟨j,hj⟩ := hp.exists_card_eq
  have hdQ : Disjoint K (Q F v) := disjoint_of_coprime_natCard (by
    rw [hj]; exact ho.coprime_two_right.pow_right j)
  obtain ⟨x,hx,hx1⟩ := K.bot_or_exists_ne_one.resolve_left hne
  let x' : c.actor := ⟨x,hKL hx⟩
  have hqx : c.quotient x' ≠ 1 := by
    intro hh
    have hmem : x' ∈ c.quotient.ker := hh
    rw [c.kernel] at hmem
    exact hx1 (disjoint_def.mp hdQ hx hmem)
  have hxo : Odd (orderOf x') := by
    simpa only [x',Subgroup.orderOf_mk] using
      ho.of_dvd_nat (_root_.orderOf_dvd_natCard (⟨x,hx⟩ : K))
  intro hCD
  have hQ : Q F v ≤ Q F m := by
    intro z hz
    exact (c.linear_core_odd_fixed h hB hS hb hactor hcentral ht htne hcomm hnot eβ
      x' (hxo.of_dvd_nat (orderOf_map_dvd c.quotient x')) hqx z hz
        (hCD (commutator_mem_commutator hz hx))).1
  apply hnot
  rw [inf_eq_right.mpr hQ]
  exact CommutingNontrivial.stabilizer_normalizes_Q F v

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource

open Subgroup
open scoped commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem full_cartan_mover_centralizes_local_quotient
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F))
    (hF : 2 < Nat.card F)
    (K : Subgroup G) [IsMulCommutative K]
    (hKE : K ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hdis : Disjoint K ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2))
    (hgen : K ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (ho : Odd (Nat.card K))
    (a : graphLocalGroup (family P) w) (hamove : (a : G) • v ≠ v)
    (x : G) (hx : x ∈ K) (hxa : Commute x (a : G)) :
    ∀ l ∈ graphLocalGroup (family P) w, ⁅x,l⁆ ∈ Q (family P) w := by
  let _ := finite_endpoints h
  let M := graphLocalGroup (family P) w
  let E := stabilizer (family P) w ⊓ stabilizer (family P) v
  let C := K ⊓ M
  let _ : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _))
    (inclusion_injective _)
  obtain ⟨T,hT⟩ := CommutingTrivial.local_edge_sylow h hB hS hvw.symm
  change (T : Subgroup M).map M.subtype = E.pCoreIn 2 at hT
  have hTN := graph_intrinsic_edge_sylow_normalizer h hB hvw.symm T hT
  have hKE' : K ≤ E := hKE.trans (inf_comm _ _).le
  obtain ⟨⟨eC⟩,_⟩ := CommutingTrivial.edge_complement_local_torus h hB hS hvw.symm e K hKE'
    (by simpa only [E,inf_comm (stabilizer (family P) w)] using hdis)
    (by simpa only [E,inf_comm (stabilizer (family P) w)] using hgen)
  have hxN : x ∈ normalizer (M : Set G) :=
    sylowGenerated_normalized _ (hKE hx).2
  let α := M.normalizerMonoidHom ⟨x,hxN⟩
  have hα (l : M) : (α l : G) = x*l*x⁻¹ := rfl
  have hαT : (T : Subgroup M).map α.toMonoidHom = T := by
    apply Subgroup.map_injective (f := M.subtype) M.subtype_injective
    rw [Subgroup.map_map]
    have he : M.subtype.comp α.toMonoidHom = (MulAut.conj x).toMonoidHom.comp M.subtype :=
      MonoidHom.ext hα
    rw [he,←Subgroup.map_map,hT]
    apply mem_normalizer_iff_map_conj_eq.mp
    exact (E.le_normalizer.trans (normalizer_le_normalizer_characteristic_image E (pCore 2 E)))
      (hKE' hx)
  have hCN : C.subgroupOf M ≤ normalizer (T : Set M) := by
    rw [←hTN]
    exact fun c hc => (hKE hc.1).1
  have hCo : Odd (Nat.card (C.subgroupOf M)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show C ≤ M from inf_le_right)).toEquiv]
    exact ho.of_dvd_nat (card_dvd_of_le (show C ≤ K from inf_le_left))
  have hCc : Nat.card (C.subgroupOf M) = Nat.card Fˣ :=
    (Nat.card_congr (subgroupOfEquivOfLe (show C ≤ M from inf_le_right)).toEquiv).trans
      (Nat.card_congr eC.toEquiv)
  have hfixC : ∀ c ∈ C.subgroupOf M, α c = c := by
    intro c hc
    apply Subtype.ext
    change x*c*x⁻¹ = c
    exact mul_inv_eq_iff_eq_mul.mpr (congrArg Subtype.val
      (mul_comm (⟨x,hx⟩ : K) (⟨c,hc.1⟩ : K)))
  have haN : a ∉ normalizer (T : Set M) := by
    rw [←hTN]
    exact hamove
  have hfixa : α a = a := Subtype.ext (mul_inv_eq_iff_eq_mul.mpr hxa.eq)
  have hqα := Matrix.SpecialLinearGroup.core_quotient_torus_mover_fixed hF e T
    (C.subgroupOf M) hCN hCo hCc α hαT hfixC a haN hfixa
  intro l hl
  let l' : M := ⟨l,hl⟩
  have he : QuotientGroup.mk' (pCore 2 M) (α l') =
      QuotientGroup.mk' (pCore 2 M) l' := by
    calc
      QuotientGroup.mk' (pCore 2 M) (α l') =
          (pCore 2 M).quotientAut α (QuotientGroup.mk' (pCore 2 M) l') :=
        (quotientAut_apply_mk (pCore 2 M) α l').symm
      _ = QuotientGroup.mk' (pCore 2 M) l' := by rw [hqα]; rfl
  have hmem := QuotientGroup.eq_iff_div_mem.mp he
  apply (CommutingTrivial.graphLocalGroup_core h w).le
  refine ⟨α l'/l',hmem,?_⟩
  change (x*l*x⁻¹)/l = ⁅x,l⁆
  simp only [div_eq_mul_inv,commutatorElement_def]

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups commutatorElement IsMulCommutative
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

theorem original_bTwo_cartan_tori_distinct
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    (K : Subgroup (G₀ L S)) [IsMulCommutative K]
    (hKE : K ≤ stabilizer F α ⊓ stabilizer F β)
    (hd : Disjoint K ((stabilizer F α ⊓ stabilizer F β).pCoreIn 2))
    (hgen : K ⊔ (stabilizer F α ⊓ stabilizer F β).pCoreIn 2 =
      stabilizer F α ⊓ stabilizer F β)
    (ho : Odd (Nat.card K))
    (g : G₀ L S) (hg : g ∈ graphLocalGroup F α)
    (hgK : g ∈ normalizer (K : Set (G₀ L S))) (hgt : g • β = t)
    (a : G₀ L S) (ha : a ∈ graphLocalGroup F β)
    (haK : a ∈ normalizer (K : Set (G₀ L S))) (hau : a • α = u) :
    K ⊓ graphLocalGroup F α ≠ K ⊓ graphLocalGroup F u ∧
      ((K ⊓ graphLocalGroup F α) ⊔ (K ⊓ graphLocalGroup F u)) ⊓
        (K ⊓ graphLocalGroup F β) ≠ ⊥ := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let _ : Finite (stabilizer F α) := by
    change Finite (MulAction.stabilizer (G₀ L S) α)
    rw [Subgroup.CosetGeometry.stabilizer_base]
    infer_instance
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hB := reduced_borel_core_sylow h
  have hS := reduced_vertex_sylow h
  have hua : u ≠ α := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self,hb] at hh
    omega
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let _ : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hk := field_gt_two_of_nonsolvable h c hactor hns
  obtain ⟨n,hn,J,fJ,finJ,hJ,⟨eJ⟩⟩ :=
    reduced_noncommuting_actor_quotients_linear h hc hne β
  let _ := fJ
  let _ := finJ
  let _ : Fintype J := Fintype.ofFinite J
  let _ : CharP J 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hJ)
  let eβ := eJ.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi J)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  have hJlarge : 2 < Nat.card J := hk.trans_le
    (c.linear_central_core_structure H hB hS hb hactor hcentral ht htne hcomm.le hnot eβ).1
  have hsep := bTwo_odd_local_tori_disjoint H hB hS c hactor hcentral
    (base_Z_ne_bot H true) K ho
  have hcore : c.actor.pCoreIn 2 = Q F α := by
    rw [hactor]
    exact CommutingTrivial.graphLocalGroup_core H α
  have hker : c.quotient.ker = pCore 2 c.actor := by
    have hkernel : c.quotient.ker = (Q F α).subgroupOf c.actor := c.kernel
    rw [hkernel,←hcore]
    exact comap_map_eq_self_of_injective c.actor.subtype_injective _
  let eA := MulEquiv.subgroupCongr hactor
  let eQ := QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)
  let eα := eQ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective c.quotient c.onto))
  obtain ⟨⟨eKa⟩,_⟩ := CommutingTrivial.edge_complement_local_torus H hB hS
    hab eα K hKE hd hgen
  have hKa : K ⊓ graphLocalGroup F α ≠ ⊥ := by
    intro he
    have hh : Nat.card ↥(K ⊓ graphLocalGroup F α) = Nat.card kˣ :=
      Nat.card_congr eKa.toEquiv
    rw [he,Nat.card_units] at hh
    have hh1 : Nat.card (⊥ : Subgroup (G₀ L S)) = 1 := Nat.card_unique
    rw [hh1] at hh
    omega
  have hneTor : K ⊓ graphLocalGroup F α ≠ K ⊓ graphLocalGroup F u := by
    intro he
    have hfixa (x : G₀ L S) (hx : x ∈ K ⊓ graphLocalGroup F α) : Commute x a := by
      have hh : ⁅a,x⁆ ∈ ((K ⊓ graphLocalGroup F α) ⊔
          (K ⊓ graphLocalGroup F (a • α))) ⊓ (K ⊓ graphLocalGroup F β) :=
        cartan_mover_commutator_mem H K (hKE.trans inf_le_right) ha haK hx
      rw [hau,←he,sup_idem] at hh
      exact (commutatorElement_eq_one_iff_mul_comm.mp (disjoint_def.mp hsep hh.1 hh.2)).symm
    have hCQ : ⁅K ⊓ graphLocalGroup F α,Q F α⁆ ≤ Q F β := by
      apply commutator_le.mpr
      intro x hx z hz
      have hQL : Q F α ≤ graphLocalGroup F β := by
        have hh := graph_Q_le_edgeCore H hab
        rw [inf_comm] at hh
        exact hh.trans (graph_intrinsic_edgeCore_le H)
      have hamove : a • α ≠ α := by rw [hau]; exact hua
      exact full_cartan_mover_centralizes_local_quotient H hB hS hab eβ hJlarge K
        hKE hd hgen ho ⟨a,ha⟩ hamove x hx.1 (hfixa x hx) z (hQL hz)
    have hgv : g • α = α := sylowGenerated_le _ hg
    have hKaMap : (K ⊓ graphLocalGroup F α).map (MulAut.conj g).toMonoidHom =
        K ⊓ graphLocalGroup F α := by
      have hh : (K ⊓ graphLocalGroup F α).map (MulAut.conj g).toMonoidHom =
          K ⊓ graphLocalGroup F (g • α) := cartan_local_conjugate H K hgK α
      simpa only [hgv] using hh
    have hCt := map_mono (f := (MulAut.conj g).toMonoidHom) hCQ
    rw [map_commutator,hKaMap,←Q_translate,←Q_translate,hgv,hgt] at hCt
    have hCD : ⁅Q F α,K ⊓ graphLocalGroup F α⁆ ≤ D F β t := by
      rw [commutator_comm]
      exact le_inf hCQ hCt
    exact bTwo_odd_subgroup_moves_core_quotient H hB hS hb c hactor hcentral ht htne
      hcomm.le hnot eβ (K ⊓ graphLocalGroup F α)
      (by rw [hactor]; exact inf_le_right)
      (ho.of_dvd_nat (card_dvd_of_le inf_le_left)) hKa hCD
  refine ⟨hneTor,?_⟩
  have hneTor' : K ⊓ graphLocalGroup F (a • α) ≠ K ⊓ graphLocalGroup F α := by
    simpa only [hau] using Ne.symm hneTor
  have hh : ((K ⊓ graphLocalGroup F α) ⊔ (K ⊓ graphLocalGroup F (a • α))) ⊓
      (K ⊓ graphLocalGroup F β) ≠ ⊥ :=
    distinct_local_tori_intersection_ne_bot H K (hKE.trans inf_le_right) ha haK hneTor'
  simpa only [hau] using hh

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

/-- The full path Cartan constructed from the original source has distinct
alpha tori and a nontrivial intersection with the beta torus. -/
theorem original_bTwo_path_cartan_distinct
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
      K ⊓ graphLocalGroup F α ≠ K ⊓ graphLocalGroup F u ∧
      ((K ⊓ graphLocalGroup F α) ⊔ (K ⊓ graphLocalGroup F u)) ⊓
        (K ⊓ graphLocalGroup F β) ≠ ⊥ := by
  obtain ⟨K,hfix,hd,hgen,ho,hcomm,hprod,⟨g,hg,hgK,hgt⟩,⟨a,ha,haK,hau⟩⟩ :=
    original_bTwo_path_cartan_transport h hc hne hb hβu ht htne hy hyne
  let _ := hcomm
  have hKE : K ≤ stabilizer F α ⊓ stabilizer F β :=
    le_inf (fun k hk => (hfix hk).1.1.1.2) (fun k hk => (hfix hk).1.1.2)
  exact ⟨K,hfix,hd,hgen,ho,hcomm,hprod,g,hg,hgK,hgt,a,ha,haK,hau,
    original_bTwo_cartan_tori_distinct h hc hne hb hβu ht htne hns K hKE hd hgen ho
      g hg hgK hgt a ha haK hau⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
