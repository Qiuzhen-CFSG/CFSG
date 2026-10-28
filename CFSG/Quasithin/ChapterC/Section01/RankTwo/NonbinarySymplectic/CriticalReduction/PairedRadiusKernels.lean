module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusPaths

/-!
# Full paired kernels in the first MS93 (5.11) contradiction

Symplectic duality compares fixed subgroups on the entire Z-layer, retaining
its central attachment. A critical seed fills any containing endpoint image
of order at most q. The resulting common commutator fixes the literal smaller
movers at the next same-color vertex, using the proved mover agreement.

Apply this comparison to the actual paired backward path. The source
conjugator carries the second full kernel over the first. If the joined
image has order at most q and its whole kernel lies in the original seed
joined with the opposite Q, both endpoint generators normalize the selected
kernel joined with that seed. The actual generating triple contradicts the
proved kernel escape. Thus the same selected pair violates at least one of
these two bounds, without any additional selection or fixed-layer premise.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), MS93 (5.11), printed p.923. Deriving both bounds from the hypothesized
q-squared radius index, the remaining (5.11)--(5.12) exclusions, and the
minimum-replacement distance-two witness remain in this reduction. This
module does not assert original-radical characteristic control.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Whole-Z duality retains every central attachment. -/
theorem Input.replacement_full_seed_fixed_antitone_of_commutator_le
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {v : Vertex d.radical} (hv : color d.radical v=false)
    (A B : Subgroup (FreeAmalgam d.radical))
    (hAS : A ≤ stabilizer d.radical v) (hBS : B ≤ stabilizer d.radical v)
    (hle : ⁅Z d.radical v,A⁆ ≤ ⁅Z d.radical v,B⁆) :
    Z d.radical v ⊓ centralizer (B : Set (FreeAmalgam d.radical)) ≤
      Z d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical)) := by
  let D := Z d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))
  have hs := h.replacement_Z_eq_U_sup_fixed d geometry hb hv
  have hDA : D ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hAS)
  have hDB : D ≤ centralizer (B : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hBS)
  have hcomm : ⁅A,U d.radical v⁆ ≤ ⁅B,U d.radical v⁆ := by
    rw [commutator_comm A,commutator_comm B,
      ←h.replacement_Z_commutator_eq_U d geometry hb hv A hAS,
      ←h.replacement_Z_commutator_eq_U d geometry hb hv B hBS]
    exact hle
  have hf := h.replacement_moving_fixed_antitone_of_commutator_le d geometry hb hv A B hAS hBS hcomm
  intro x hx
  have hDU : D ≤ normalizer (U d.radical v : Set (FreeAmalgam d.radical)) :=
    (inf_le_left.trans (Z_le_stabilizer _ _)).trans (U_normalized v)
  have hx' : x ∈ (U d.radical v : Set (FreeAmalgam d.radical))*(D : Set (FreeAmalgam d.radical)) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hDU,←hs]
    exact hx.1
  obtain ⟨u,hu,c,hc,rfl⟩ := hx'
  have huB : u ∈ centralizer (B : Set (FreeAmalgam d.radical)) := by
    have hh := (centralizer (B : Set (FreeAmalgam d.radical))).mul_mem hx.2
      ((centralizer (B : Set (FreeAmalgam d.radical))).inv_mem (hDB hc))
    simpa only [mul_inv_cancel_right] using hh
  exact ⟨hx.1,(centralizer (A : Set (FreeAmalgam d.radical))).mul_mem (hf ⟨hu,huB⟩).2 (hDA hc)⟩

omit h in
private theorem commutator_eq_of_kernel_join {G : Type*} [Group G]
    (Z Q A T : Subgroup G) (hAT : A ≤ T)
    (hQ : Q ≤ centralizer (Z : Set G)) (hAQ : A ≤ normalizer (Q : Set G))
    (he : A ⊔ Q=T ⊔ Q) : ⁅Z,A⁆=⁅Z,T⁆ := by
  apply le_antisymm (commutator_mono le_rfl hAT)
  apply commutator_le.mpr
  intro z hz t ht
  have ht' : t ∈ (A : Set G)*(Q : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right A Q hAQ,he]
    exact mem_sup_left ht
  obtain ⟨a,ha,q,hq,rfl⟩ := ht'
  have hc : ⁅z,q⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hQ hq z hz)
  rw [commutatorElement_mul_right_eq_mul_conj,hc,mul_one,mul_inv_cancel_right]
  exact commutator_mem_commutator hz ha

/-- A critical seed fills a local image of order at most q, including the
full preimage kernel and the displacement of the whole endpoint seed. -/
theorem Input.replacement_critical_seed_saturates_small_image
    {geometry : Geometry d.radical} {v e : Vertex d.radical}
    (path : CriticalPath d.radical geometry v e) (hb : 4 ≤ geometry.b d.radical)
    (T : Subgroup (FreeAmalgam d.radical)) (hvT : Z d.radical v ≤ T)
    (hTS : T ≤ stabilizer d.radical e)
    (hi : (Q d.radical e).relIndex T ≤ Nat.card F) :
    Z d.radical v ⊔ Q d.radical e=T ⊔ Q d.radical e ∧
      ⁅Z d.radical v,Z d.radical e⁆=⁅T,Z d.radical e⁆ ∧
      (Q d.radical e).relIndex (Z d.radical v)=Nat.card F ∧
      (Q d.radical v).relIndex (Z d.radical e)=Nat.card F := by
  obtain ⟨E,hE,f,hf,hfQ,hidx⟩ := h.replacement_inner_natural_indices d geometry hb path.end_color
  let S := stabilizer d.radical e
  let A := (Z d.radical v).subgroupOf S
  let T₀ := T.subgroupOf S
  have hvS := hvT.trans hTS
  have image_card (B : Subgroup (FreeAmalgam d.radical)) (hB : B ≤ S) :
      Nat.card ((B.subgroupOf S).map f)=(Q d.radical e).relIndex B := by
    rw [←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker (B.subgroupOf S) S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hB] at hh
    exact hh.symm
  have hlo := (h.replacement_critical_indices_ge_field d path (by omega)).1
  have himage : A.map f=T₀.map f := eq_of_le_of_card_ge (map_mono (comap_mono hvT)) (by
    rw [image_card T hTS,image_card (Z d.radical v) hvS]
    exact hi.trans hlo)
  have heq := congrArg (Subgroup.map S.subtype) (congrArg (Subgroup.comap f) himage)
  rw [comap_map_eq,comap_map_eq,Subgroup.map_sup,Subgroup.map_sup,
    map_subgroupOf_eq_of_le hvS,map_subgroupOf_eq_of_le hTS,hfQ] at heq
  have hsmall : (Q d.radical e).relIndex (Z d.radical v) ≤ Nat.card F := by
    rw [←image_card (Z d.radical v) hvS]
    change Nat.card (A.map f) ≤ _
    rw [himage,image_card T hTS]
    exact hi
  have hvindex := le_antisymm hsmall hlo
  have heindex := (h.replacement_critical_indices_equal d path hb).symm.trans hvindex
  refine ⟨heq,?_,hvindex,heindex⟩
  rw [commutator_comm (Z d.radical v),commutator_comm T]
  exact commutator_eq_of_kernel_join _ _ _ _ hvT
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes e path.end_color)))
    (hvS.trans (Q_normalized _ e)) heq


/-- A field-sized critical commutator fixes the literal first mover and
lies in the complete seed at the next same-color vertex. -/
theorem Input.replacement_field_critical_commutator_le_neighbor_fixed
    {geometry : Geometry d.radical} {v e : Vertex d.radical}
    (path : CriticalPath d.radical geometry v e) (hb : 4 < geometry.b d.radical)
    (hi : (Q d.radical e).relIndex (Z d.radical v) ≤ Nat.card F) :
    ⁅Z d.radical v,Z d.radical e⁆ ≤ Z d.radical (path.walk.getVert 2) ⊓
      centralizer (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  let a := path.walk.getVert 2
  let t := path.walk.getVert 1
  let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical t) (Nat.card F^2)
  let D := ⁅Z d.radical v,Z d.radical e⁆
  have hvt : Adjacent d.radical v t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hat : Adjacent d.radical a t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 1 < path.walk.length)))
  have ha : color d.radical a=false := (path.vertex_color
    (by rw [path.length_eq_b]; omega : 2 ≤ path.walk.length)).mpr (by decide)
  have heS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have heT : Z d.radical e ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt _ e (geometry.exists_critical e path.end_color)
    rw [geometry.distance_constant e path.end_color,SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
    change geometry.b d.radical-1 < geometry.b d.radical
    omega
  have hvS : Z d.radical v ≤ stabilizer d.radical e :=
    Z_le_stabilizer_of_dist_le v (geometry.exists_critical v path.start_color) path.critical.1.le
  have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) e path.end_color
  have hfixed : Z d.radical v ⊓ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) =
      Z d.radical v ⊓ Q d.radical e := by
    rw [←hC]
    ext x
    exact ⟨fun hx => ⟨hx.1,hvS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  let := finite_Z d.radical v
  have hiU : (centralizer (Z d.radical e : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical v) ≤ Nat.card F := by
    apply (relIndex_le_of_le_right (U_le_Z v) index_ne_zero_of_finite).trans
    rwa [←inf_relIndex_left,hfixed,inf_relIndex_left]
  have hDC : D ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    change ⁅Z d.radical v,Z d.radical e⁆ ≤ _
    rw [h.replacement_Z_commutator_eq_U d geometry hb.le path.start_color _ heS]
    exact h.replacement_small_mover_join_centralizes_field_displacement d geometry hb.le
      path.start_color hvt _ heT hiU
  have hequal : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)=J := by
    simpa only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero]
      using h.replacement_mover_agreement_of_four_lt d ⟨v,e,path⟩ hb
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hQaJ : Q d.radical a ≤ J := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR,hequal] at hh
  have hsmall : (Q d.radical e).relIndex (Z d.radical v) < Nat.card F^2 :=
    hi.trans_lt (by have hq : 1<Nat.card F := Finite.one_lt_card; nlinarith)
  have hsmall' : (Q d.radical v).relIndex (Z d.radical e) < Nat.card F^2 := by
    rw [←h.replacement_critical_indices_equal d path hb.le]
    exact hsmall
  obtain ⟨g,hg,hga⟩ := stabilizer_transitive_neighbors d.radical t
    (adjacent_symm _ hvt) (adjacent_symm _ hat)
  have ht : act d.radical g t=t := hg
  have hsmallg : (Q d.radical (act d.radical g v)).relIndex
      (Z d.radical (act d.radical g e)) < Nat.card F^2 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hsmall'
  have hgat : Adjacent d.radical (act d.radical g v) t := by
    rw [←ht]
    exact (adjacent_act_iff d.radical g v t).mpr hvt
  have hXa : X d.radical a=Z d.radical a := by
    have hh := h.replacement_root_X_eq_Z d (path.act g) hb.le hgat hsmallg
    rwa [hga] at hh
  have hDZ : D ≤ Z d.radical v := critical_commutator_le_start_seed path
  have hDQ : D ≤ Q d.radical a :=
    (hDZ.trans (le_sup_left.trans (neighbor_seed_join_le_radius hat hvt))).trans
      (geometry.V_le_Q (by omega) a ha)
  have hDX : D ≤ X d.radical a := by
    intro y hy
    apply mem_omegaCenter_iff.mpr
    exact ⟨hDQ hy,(mem_omegaCenter_iff.mp
      (geometry.omega_bound v path.start_color (by
        rw [geometry.distance_constant v path.start_color]; exact (by omega : 0 < geometry.b d.radical)) (hDZ hy))).2.1,
      centralizer_le hQaJ (hDC hy)⟩
  exact le_inf (hDX.trans_eq hXa) hDC


/-- The selected pair's small joined image controls the entire conjugate
kernel. When both seeds escape, their common full commutator is fixed by
the original vertex, through the very same paired mover equality. -/
theorem Input.replacement_paired_radius_kernel_conjugate_containment
    {geometry : Geometry d.radical} (p p' : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hl : BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F)) p p')
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical p.first)
    (hfixed : (Z d.radical p.first ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical p'.first) (Q d.radical p'.first)
          (Q d.radical (p'.path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical (act d.radical x p'.first))
          (Q d.radical (act d.radical x p'.first))
          (Q d.radical (act d.radical x (p'.path.walk.getVert 1))) (Nat.card F^2) :
            Set (FreeAmalgam d.radical)) =
          Z d.radical p.first ⊓ centralizer (stabilizer d.radical p.first : Set (FreeAmalgam d.radical)))
    (hi : (Q d.radical p'.last).relIndex
      (Z d.radical p'.first ⊔ Z d.radical (act d.radical x p'.first)) ≤ Nat.card F) :
    Z d.radical p'.first ⊓ Q d.radical p'.last ≤
      (Z d.radical (act d.radical x p'.first) ⊓ Q d.radical p'.last).map
        (MulAut.conj x).toMonoidHom ∧
      (¬ Z d.radical (act d.radical x p'.first) ≤ Q d.radical p'.last →
        ⁅Z d.radical p'.first,Z d.radical p'.last⁆ =
          ⁅Z d.radical (act d.radical x p'.first),Z d.radical p'.last⁆ ∧
        ⁅Z d.radical p'.first,Z d.radical p'.last⁆ ≤
          centralizer (stabilizer d.radical p.first : Set (FreeAmalgam d.radical))) := by
  let v := p'.first
  let w := act d.radical x v
  let e := p'.last
  let f := (MulAut.conj x).toMonoidHom
  have hwmap : (Z d.radical w).map f=Z d.radical v := by
    simpa only [inv_inv,←act_mul,mul_inv_cancel,act_one] using
      (Z_act d.radical x⁻¹ (act d.radical x v)).symm
  by_cases hwQ : Z d.radical w ≤ Q d.radical e
  · refine ⟨?_,fun hn => (hn hwQ).elim⟩
    rw [inf_eq_left.mpr hwQ,hwmap]
    exact inf_le_left
  obtain ⟨t,hchoice,hat,hvt,hfirst⟩ := hl.choice
  have hax : act d.radical x p.first=p.first := hx
  have hatx : Adjacent d.radical p.first (act d.radical x t) := by
    rw [←hax]
    exact (adjacent_act_iff d.radical x p.first t).mpr hat
  have hwtx : Adjacent d.radical w (act d.radical x t) :=
    (adjacent_act_iff d.radical x v t).mpr hvt
  have hnot : ¬ Z d.radical w ≤ Q d.radical (p.path.walk.getVert (p.path.walk.length-2)) := by
    simpa only [p.path.length_eq_b,←hl.last_eq] using hwQ
  have heq : p.path.walk.getVert (p.path.walk.length-2)=e := by
    rw [p.path.length_eq_b,←hl.last_eq]
  have hex := exists_backward_path_of_not_le geometry (by omega) p.path hatx hwtx hnot
  rw [heq] at hex
  obtain ⟨back',back_first,hbackover⟩ := hex
  have back_two : back'.walk.getVert 2=p.first := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hbackover 0 (by omega)
  have p'_two : p'.path.walk.getVert 2=p.first := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hl.overlap 0 (by omega)
  let Y := Z d.radical v ⊔ Z d.radical w
  have hvS : Z d.radical v ≤ stabilizer d.radical e :=
    Z_le_stabilizer_of_dist_le v (geometry.exists_critical v p'.path.start_color) p'.path.critical.1.le
  have hwS : Z d.radical w ≤ stabilizer d.radical e :=
    Z_le_stabilizer_of_dist_le w (geometry.exists_critical w back'.start_color) back'.critical.1.le
  have hYS : Y ≤ stabilizer d.radical e := sup_le hvS hwS
  obtain ⟨_,hc₁,hi₁,_⟩ := h.replacement_critical_seed_saturates_small_image d p'.path hb.le Y le_sup_left hYS hi
  obtain ⟨_,hc₂,hi₂,_⟩ := h.replacement_critical_seed_saturates_small_image d back' hb.le Y le_sup_right hYS hi
  have hcommon : ⁅Z d.radical v,Z d.radical e⁆=⁅Z d.radical w,Z d.radical e⁆ := hc₁.trans hc₂.symm
  have hfixed₁ := h.replacement_field_critical_commutator_le_neighbor_fixed d p'.path hb hi₁.le
  have hfixed₂ := h.replacement_field_critical_commutator_le_neighbor_fixed d back' hb hi₂.le
  rw [p'_two] at hfixed₁
  rw [back_two,back_first,←hfirst] at hfixed₂
  have hcentral : ⁅Z d.radical v,Z d.radical e⁆ ≤
      centralizer (stabilizer d.radical p.first : Set (FreeAmalgam d.radical)) := by
    have hboth : ⁅Z d.radical v,Z d.radical e⁆ ≤
        (Z d.radical p.first ⊓ centralizer
          (Subgroup.SmallMover.join (U d.radical p'.first) (Q d.radical p'.first)
            (Q d.radical (p'.path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
          centralizer (Subgroup.SmallMover.join (U d.radical (act d.radical x p'.first))
            (Q d.radical (act d.radical x p'.first))
            (Q d.radical (act d.radical x (p'.path.walk.getVert 1))) (Nat.card F^2) :
              Set (FreeAmalgam d.radical)) :=
      le_inf hfixed₁ (hcommon.le.trans (hfixed₂.trans inf_le_right))
    rw [hfixed] at hboth
    exact hboth.trans inf_le_right
  have hDmap : (⁅Z d.radical v,Z d.radical e⁆).map f=⁅Z d.radical v,Z d.radical e⁆ :=
    mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hcentral hx))
  have hcomm : ⁅Z d.radical v,(Z d.radical e).map f⁆=⁅Z d.radical v,Z d.radical e⁆ := by
    calc
      ⁅Z d.radical v,(Z d.radical e).map f⁆ =
          ⁅(Z d.radical w).map f,(Z d.radical e).map f⁆ := by rw [hwmap]
      _ = (⁅Z d.radical w,Z d.radical e⁆).map f := (map_commutator _ _ f).symm
      _ = (⁅Z d.radical v,Z d.radical e⁆).map f := by rw [←hcommon]
      _ = ⁅Z d.radical v,Z d.radical e⁆ := hDmap
  have heS := p'.path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hfS : (Z d.radical e).map f ≤ stabilizer d.radical v := by
    have hh := map_mono (f := f) (back'.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical))
    have he : (stabilizer d.radical w).map f=stabilizer d.radical v := by
      simpa only [inv_inv,←act_mul,mul_inv_cancel,act_one] using
        (stabilizer_act d.radical x⁻¹ (act d.radical x v)).symm
    rwa [he] at hh
  have hkernel := h.replacement_full_seed_fixed_antitone_of_commutator_le d geometry hb.le
    p'.path.start_color ((Z d.radical e).map f) (Z d.radical e) hfS heS hcomm.le
  have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) e p'.path.end_color
  have hfix (u : Vertex d.radical) (hu : Z d.radical u ≤ stabilizer d.radical e) :
      Z d.radical u ⊓ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) =
        Z d.radical u ⊓ Q d.radical e := by
    rw [←hC]
    ext y
    exact ⟨fun hy => ⟨hy.1,hu hy.1,hy.2⟩,fun hy => ⟨hy.1,hy.2.2⟩⟩
  have hmapfix : (Z d.radical w ⊓ centralizer (Z d.radical e : Set (FreeAmalgam d.radical))).map f =
      Z d.radical v ⊓ centralizer ((Z d.radical e).map f : Set (FreeAmalgam d.radical)) := by
    rw [←map_inf_centralizer_of_injective f (MulAut.conj x).injective,hwmap]
  rw [hfix v hvS,←hmapfix,hfix w hwS] at hkernel
  exact ⟨hkernel,fun _ => ⟨hcommon,hcentral⟩⟩

/-- The actual paired source selection cannot have both a field-sized
joined endpoint image and its full kernel in the original seed-kernel
product. Both endpoint normalizations use the same source conjugator. -/
theorem Input.replacement_paired_radius_image_kernel_obstruction
    {geometry : Geometry d.radical} (p p' : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hl : BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F)) p p') :
    ∃ x ∈ Ltilde d.radical p.first,
      let Y := Z d.radical p'.first ⊔ Z d.radical (act d.radical x p'.first)
      Nat.card F < (Q d.radical p'.last).relIndex Y ∨
        ¬ Y ⊓ Q d.radical p'.last ≤ Z d.radical p.first ⊔ Q d.radical p.last := by
  obtain ⟨t,hchoice,hat,hvt,hfirst⟩ := hl.choice
  obtain ⟨x,hx,hatx,hvtx,hix,hgen,hgen',hfixed⟩ := hchoice.2
  refine ⟨x,hx,?_⟩
  dsimp only
  by_contra! hbad
  obtain ⟨hi,hplace⟩ := hbad
  let a := p.first
  let z := p.last
  let v := p'.first
  let w := act d.radical x v
  let e := p'.last
  let Y := Z d.radical v ⊔ Z d.radical w
  let K₁ := Z d.radical v ⊓ Q d.radical e
  let K₂ := Z d.radical w ⊓ Q d.radical e
  let f := (MulAut.conj x).toMonoidHom
  have hxS : x ∈ stabilizer d.radical a := Ltilde_le_stabilizer a hx
  have ha : act d.radical x a=a := hxS
  have hZa : (Z d.radical a).map f=Z d.radical a := by
    have ha' : act d.radical x⁻¹ a=a := (stabilizer d.radical a).inv_mem hxS
    simpa only [ha',inv_inv] using (Z_act d.radical x⁻¹ a).symm
  have hSa : (stabilizer d.radical a).map f=stabilizer d.radical a := by
    have ha' : act d.radical x⁻¹ a=a := (stabilizer d.radical a).inv_mem hxS
    simpa only [ha',inv_inv] using (stabilizer_act d.radical x⁻¹ a).symm
  have hYV : Y ≤ V d.radical a := sup_le
    (le_sup_left.trans (neighbor_seed_join_le_radius hat hvt))
    (le_sup_left.trans (neighbor_seed_join_le_radius hatx hvtx))
  let := finite_stabilizer d.radical a
  let : Finite Y := Finite.of_injective
    (inclusion (hYV.trans ((geometry.V_le_Q (by omega) a p.path.start_color).trans
      (fun _ hy => hy.1)))) (inclusion_injective _)
  have hi₁ : (Q d.radical e).relIndex (Z d.radical v) ≤ Nat.card F :=
    (relIndex_le_of_le_right (show Z d.radical v ≤ Y from le_sup_left)
      index_ne_zero_of_finite).trans hi
  have hfixed' := hfixed
  rw [←hfirst] at hfixed'
  obtain ⟨hKmap,_⟩ := h.replacement_paired_radius_kernel_conjugate_containment
    d p p' hb hl x hxS hfixed' hi
  have hK₁ : K₁ ≤ Z d.radical a ⊔ Q d.radical z :=
    (inf_le_inf le_sup_left le_rfl).trans hplace
  have hK₂ : K₂ ≤ Z d.radical a ⊔ Q d.radical z :=
    (inf_le_inf le_sup_right le_rfl).trans hplace
  have haS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a p.path.start_color)
      p.path.critical.1.le
  have hQaC : Q d.radical z ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes z p.path.end_color))
  have hproduct : ⁅Z d.radical a ⊔ Q d.radical z,Z d.radical z⁆ ≤ Z d.radical a := by
    rw [commutator_comm]
    rw [←commutator_eq_of_kernel_join (Z d.radical z) (Q d.radical z)
      (Z d.radical a) (Z d.radical a ⊔ Q d.radical z) le_sup_left hQaC
      (haS.trans (Q_normalized _ z)) (by rw [sup_assoc,sup_idem])]
    rw [commutator_comm]
    exact critical_commutator_le_start_seed p.path
  have hd₁ : ⁅K₁,Z d.radical z⁆ ≤ Z d.radical a :=
    (commutator_mono hK₁ le_rfl).trans hproduct
  have hd₂ : ⁅K₂,Z d.radical z⁆ ≤ Z d.radical a :=
    (commutator_mono hK₂ le_rfl).trans hproduct
  have hd₂map : ⁅K₂.map f,(Z d.radical z).map f⁆ ≤ Z d.radical a := by
    have hh := map_mono hd₂ (f := f)
    rwa [map_commutator,hZa] at hh
  have hdmap : ⁅K₁,(Z d.radical z).map f⁆ ≤ Z d.radical a :=
    (commutator_mono hKmap le_rfl).trans hd₂map
  have hzS := p.path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hzmapS : (Z d.radical z).map f ≤ stabilizer d.radical a := by
    have hh := map_mono hzS (f := f)
    rwa [hSa] at hh
  have hn₁ := normalizes_sup_of_displacement _ _ _
    (hzS.trans (Z_normalized d.radical a)) hd₁
  have hn₂ := normalizes_sup_of_displacement _ _ _
    (hzmapS.trans (Z_normalized d.radical a)) hdmap
  have hJn := h.replacement_backward_small_mover_normalizes_kernel d p p' hb hl hi₁
  rw [hfirst] at hJn
  exact h.replacement_paired_radius_kernel_not_normal d p hb hchoice hat hvt
    (Q d.radical e) hi₁ (hgen ▸ sup_le (sup_le hJn hn₁) hn₂)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
