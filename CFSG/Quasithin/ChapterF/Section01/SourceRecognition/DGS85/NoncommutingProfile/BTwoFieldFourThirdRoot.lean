module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoKernelCubicAction
public import Theory.SpecificGroups.SL2.FieldFourThirdRoot

/-!
# The third-root obstruction for the actual terminal cubic

In the binary-alpha, field-four-beta case of DGS (10.8), the two original
centralizing root factors meet distinct beta roots. The entire beta
centralizer is nontransitive by graph faithfulness, so its literal quotient
image is proper. A cubic fixing another alpha neighbor normalizes that
neighbor's root. The field-four third-root theorem makes the centralizer
meet this root trivially, giving C_Q_delta(x) ≤ Q_beta.

If the tested residual element x lay in Q_delta, the already proved cubic
core-section action would put it in every adjacent core. Transporting an
original radius/core factor to delta gives a full root image of order four.
Its centralizer loses at most a factor of two, but the third-root bound
makes its image trivial. This contradiction proves x is outside Q_delta.

The original-source theorem retains one opposite-center conjugator, both
centralizing factors, the actual order-three actor, its full radius-one
kernel membership, and the reduced-to-original inclusion. The same bound
also proves that this cubic moves the original alpha neighbor. The companion
terminal-separation module supplies the missing core placement from the
source hypotheses and applies the contradiction proved here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.7)--(10.8), printed pp.159--161, especially the third-root paragraph
on p.161.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting
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

namespace Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private theorem cubic_centralizer_core_bound
    (h : HypothesisF11 L S) {v a b δ : Vertex F}
    (ha : (graph F).Adj v a) (hb : (graph F).Adj v b) (hδ : (graph F).Adj v δ)
    (hab : a≠b)
    (e : (graphLocalGroup F v⧸pCore 2 (graphLocalGroup F v))≃*SL(2,K))
    (hK : Nat.card K=4)
    (A B : Subgroup (G₀ L S)) (hA : A≤Q F a) (hB : B≤Q F b)
    (hAc : Nat.card K≤2*(Q F v).relIndex A)
    (hBc : Nat.card K≤2*(Q F v).relIndex B)
    (x : G₀ L S) (hAC : A≤centralizer ({x}:Set (G₀ L S)))
    (hBC : B≤centralizer ({x}:Set (G₀ L S)))
    (hnt : ¬∀ z : Vertex F, (graph F).Adj v z →
      ∃ g∈graphLocalGroup F v⊓centralizer ({x}:Set (G₀ L S)), g • a=z)
    (d : G₀ L S) (hd : d∈graphLocalGroup F v) (hdo : orderOf d=3)
    (hdx : d∈centralizer ({x}:Set (G₀ L S))) (hdδ : d • δ=δ) :
    Q F δ⊓centralizer ({x}:Set (G₀ L S))≤Q F v := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let M := graphLocalGroup F v
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let q : M →* SL(2,K) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker=(Q F v).subgroupOf M := by
    have hc : (Q F v).subgroupOf M=pCore 2 M := graph_intrinsic_core H v
    rw [hc]
    ext x
    change e (QuotientGroup.mk' (pCore 2 M) x)=1 ↔ x∈pCore 2 M
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let earlier := reducedFullEarlierLocalTheorems h
  obtain ⟨R,hR⟩ := CommutingNontrivial.source_edge_core_local_sylow H
    (reduced_borel_core_sylow h) earlier ha
  obtain ⟨T,hT⟩ := CommutingNontrivial.source_edge_core_local_sylow H
    (reduced_borel_core_sylow h) earlier hb
  change Sylow 2 M at R T
  change (R:Subgroup M).map M.subtype=_ at hR
  change (T:Subgroup M).map M.subtype=_ at hT
  have hAR : A≤(R:Subgroup M).map M.subtype := by
    rw [hR]
    exact hA.trans (by simpa only [inf_comm,reducedFamily] using graph_Q_le_edgeCore H ha.symm)
  have hBT : B≤(T:Subgroup M).map M.subtype := by
    rw [hT]
    exact hB.trans (by simpa only [inf_comm,reducedFamily] using graph_Q_le_edgeCore H hb.symm)
  have hAM : A≤M := hAR.trans (map_subtype_le _)
  have hBM : B≤M := hBT.trans (map_subtype_le _)
  have hAi : A.subgroupOf M≤R := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hAR hx
    exact (Subtype.ext he : y=x) ▸ hy
  have hBi : B.subgroupOf M≤T := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hBT hx
    exact (Subtype.ext he : y=x) ▸ hy
  let R' := R.mapSurjective (f:=q) hq
  let T' := T.mapSurjective (f:=q) hq
  have hne : R'≠T' := by
    intro he
    have hh := congrArg (fun U : Sylow 2 SL(2,K) => (U:Subgroup SL(2,K)).comap q) he
    change ((R:Subgroup M).map q).comap q=((T:Subgroup M).map q).comap q at hh
    have hkR : q.ker≤(R:Subgroup M) := by
      rw [hk]
      have hc : (Q F v).subgroupOf M=pCore 2 M := graph_intrinsic_core H v
      rw [hc]
      exact pCore_isPGroup.le_sylow_of_normal R
    have hkT : q.ker≤(T:Subgroup M) := by
      rw [hk]
      have hc : (Q F v).subgroupOf M=pCore 2 M := graph_intrinsic_core H v
      rw [hc]
      exact pCore_isPGroup.le_sylow_of_normal T
    rw [comap_map_eq_self hkR,comap_map_eq_self hkT] at hh
    have hec := congrArg (map M.subtype) hh
    rw [hR,hT] at hec
    exact hab (graph_intrinsic_edgeCore_unique_neighbor H (reduced_borel_core_sylow h)
      ha hb (hec ▸ (pCoreIn_le 2 _).trans inf_le_right))
  obtain ⟨U,hU⟩ := CommutingNontrivial.source_edge_core_local_sylow H
    (reduced_borel_core_sylow h) earlier hδ
  change Sylow 2 M at U
  change (U:Subgroup M).map M.subtype=_ at hU
  have hδU : Q F δ≤(U:Subgroup M).map M.subtype := by
    rw [hU]
    simpa only [inf_comm,reducedFamily] using graph_Q_le_edgeCore H hδ.symm
  have hδM : Q F δ≤M := hδU.trans (map_subtype_le _)
  let U' := U.mapSurjective (f:=q) hq
  let A' := (A.subgroupOf M).map q
  let B' := (B.subgroupOf M).map q
  have hca : Nat.card A'=(Q F v).relIndex A :=
    Representation.BinaryConjugationSection.actor_image_card_eq_relIndex M (Q F v) A q hk hAM
  have hcb : Nat.card B'=(Q F v).relIndex B :=
    Representation.BinaryConjugationSection.actor_image_card_eq_relIndex M (Q F v) B q hk hBM
  let C := M⊓centralizer ({x}:Set (G₀ L S))
  let C' := (C.subgroupOf M).map q
  have hAC' : A'≤C' := map_mono (by intro z hz; exact ⟨z.property,hAC hz⟩)
  have hBC' : B'≤C' := map_mono (by intro z hz; exact ⟨z.property,hBC hz⟩)
  have hAn : A'≠⊥ := by intro he; rw [←hca,he,card_bot,hK] at hAc; omega
  have hBn : B'≠⊥ := by intro he; rw [←hcb,he,card_bot,hK] at hBc; omega
  have hproper : C'≠⊤ := by
    intro he
    have hcover : C.subgroupOf M⊔q.ker=⊤ := by
      have hh := congrArg (comap q) he
      simpa only [C',comap_map_eq,comap_top] using hh
    have hfull : C⊔Q F v=M := by
      have hh := congrArg (map M.subtype) hcover
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show C≤M from inf_le_left),hk,
        map_subgroupOf_eq_of_le (show Q F v≤M from pGroup_le_sylowGenerated _ _
          (Q_le_stabilizer F v) (isPGroup_pCoreIn 2 _)),←MonoidHom.range_eq_map,range_subtype] at hh
      exact hh
    apply hnt
    intro z hz
    obtain ⟨g,hg,hgz⟩ := graphLocalGroup_transitive H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) v ⟨a,ha⟩ ⟨z,hz⟩
    change g • a=z at hgz
    have hn : C≤normalizer (Q F v:Set (G₀ L S)) :=
      inf_le_left.trans ((sylowGenerated_le _).trans
        (CommutingNontrivial.stabilizer_normalizes_Q F v))
    have hp : g∈(C:Set (G₀ L S))*(Q F v:Set (G₀ L S)) := by
      rw [←coe_mul_of_left_le_normalizer_right C (Q F v) hn,hfull]
      exact hg
    obtain ⟨j,hj,r,hr,rfl⟩ := hp
    have hrfix : r • a=a := ((source_Z_Q_U H v).2.trans
      ((ballKernel_one_le_edge F ha).trans inf_le_right)) hr
    exact ⟨j,hj,by simpa only [mul_smul,hrfix] using hgz⟩
  let dM : M := ⟨d,hd⟩
  have hdq : q dM≠1 := by
    intro he
    have hdQ : d∈Q F v := show dM∈(Q F v).subgroupOf M from hk ▸ he
    have ho := (isPGroup_pCoreIn 2 (stabilizer F v)).orderOf_coprime
      (show Nat.Coprime 2 3 from by decide) (⟨d,hdQ⟩:Q F v)
    have horder : orderOf (⟨d,hdQ⟩:Q F v)=3 :=
      (orderOf_injective (Q F v).subtype (Q F v).subtype_injective _).symm.trans hdo
    change Nat.Coprime (orderOf (⟨d,hdQ⟩:Q F v)) 3 at ho
    rw [horder] at ho
    norm_num at ho
  have hd3 : (q dM)^3=1 := by
    rw [←map_pow]
    have hh : dM^3=1 := Subtype.ext (hdo ▸ pow_orderOf_eq_one d)
    rw [hh,map_one]
  have hdU : dM∈normalizer (U:Set M) := by
    have he := graph_intrinsic_edge_sylow_normalizer H (reduced_borel_core_sylow h) hδ U hU
    change (stabilizer F δ).subgroupOf M=normalizer (U:Set M) at he
    rw [←he]
    exact hdδ
  have hdU' : q dM∈normalizer (U':Set SL(2,K)) :=
    le_normalizer_map q (mem_map_of_mem q hdU)
  have hbot := Matrix.SpecialLinearGroup.field_four_cubic_third_root_trivial hK C' hproper
    R' T' U' hne A' B' (map_mono hAi) (map_mono hBi) hAC' hBC' hAn hBn
    (q dM) (mem_map_of_mem q (show dM∈C.subgroupOf M from ⟨hd,hdx⟩)) hdq hd3 hdU'
  intro z hz
  let zM : M := ⟨z,hδM hz.1⟩
  have hzU : zM∈U := by
    obtain ⟨w,hw,he⟩ := hδU hz.1
    exact (Subtype.ext he : w=zM) ▸ hw
  have hzq : q zM=1 := mem_bot.mp (hbot ▸
    (show q zM∈C'⊓(U':Subgroup SL(2,K)) from
      ⟨mem_map_of_mem q (show zM∈C.subgroupOf M from ⟨zM.property,hz.2⟩),
        mem_map_of_mem q hzU⟩))
  exact show zM∈(Q F v).subgroupOf M from hk ▸ hzq

/-- The same terminal cubic moves the original alpha neighbor and forces
the new alpha-core centralizer into the beta core. The third-root
contradiction places the tested residual element outside the new alpha
core, with all original markings kept. -/
theorem original_bTwo_field_four_terminal_third_root_moving
    {K₀ : Type*} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F (base F false) u)
    (hne : ⁅Z F (base F false),Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj (base F true) u)
    (ht : (graph F).Adj (base F false) t) (htne : t≠base F true)
    (e₀ : (L 0⧸pCore 2 (L 0))≃*PSL(2,K₀)) (hK₀ : Nat.card K₀=2)
    (e : (L 1⧸pCore 2 (L 1))≃*PSL(2,K))
    (hK : Nat.card K=4)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map (G₀ L S).subtype≠
      (Z F (base F false)).map (G₀ L S).subtype) :
    ∃ g∈graphLocalGroup F (base F false), g • base F true=t ∧
      let ι := (G₀ L S).subtype
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      W₀⊔Q₀=enlargedEndpoint L S 0 ∧
      R₀=(D₀⊓(Q F u).map ι)⊓(Q F (g • u)).map ι ∧ R₀≠⊥ ∧
      ∀ y : Vertex F, (graph F).Adj u y → y≠base F true →
        ∀ x∈R₀⊓(Q F y).map ι, x≠1 →
          ∃ d∈graphLocalGroup F (base F true), orderOf d=3 ∧ orderOf (ι d)=3 ∧
            ι d∈(((V F t 1).map ι⊓Q₀)⊓centralizer ({x}:Set G))⊔
              (((V F y 1).map ι⊓(Q F u).map ι)⊓centralizer ({x}:Set G)) ∧
            ι d∈centralizer ({x}:Set G) ∧
            ∃ δ : Vertex F, (graph F).Adj (base F true) δ ∧
              δ≠base F false ∧ d∈ballKernel F δ 1 ∧
              d • base F false≠base F false ∧
              ((Q F δ).map ι⊓centralizer ({x}:Set G)≤Q₁) ∧
              x∉(Q F δ).map ι ∧
              ∀ ρ : Vertex F, (graph F).Adj δ ρ →
                d∈graphLocalGroup F ρ ∧
                  ∀ z∈(Q F δ).map ι, ⁅z,ι d⁆∈Q₁⊓(Q F ρ).map ι →
                    z∈Q₁⊓(Q F ρ).map ι := by
  obtain ⟨g,hg,hgt,hW,hfour,hRne,hcubic⟩ :=
    original_bTwo_field_four_terminal_cubic_action h hc hne hb hβu ht htne e₀ hK₀ e hK hD
  obtain ⟨g₁,hg₁,hg₁t,hW₁,hfour₁,hRne₁,hrows₁,hsmall⟩ :=
    original_bTwo_alpha_binary_residual_centralizers h hc hne hb hβu ht htne e₀ hK₀ e hD
  refine ⟨g,hg,hgt,hW,hfour,hRne,?_⟩
  intro y hy hyne x hx hx1
  obtain ⟨d,hd,hdo,hdorig,hdroots,hdcentral,δ,hδ,hδne,hdk,hact⟩ :=
    hcubic y hy hyne x hx hx1
  refine ⟨d,hd,hdo,hdorig,hdroots,hdcentral,δ,hδ,hδne,hdk,?_⟩
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let ι := (G₀ L S).subtype
  let α := base F false
  let β := base F true
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let W := Z F u⊔Z F (g • u)
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hQam : (Q F α).map ι=Q₀ := reduced_base_Q_map h false
  have hQbm : (Q F β).map ι=Q₁ := reduced_base_Q_map h true
  obtain ⟨r,hr,hrx⟩ := show x∈(Q F β).map ι from hQbm.symm ▸ hx.1.1.1
  have hrt : r∈Q F t := by
    obtain ⟨z,hz,hzx⟩ := hx.1.1.2
    exact (G₀ L S).subtype_injective (hzx.trans hrx.symm) ▸ hz
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  obtain ⟨_,_,hDQ,_⟩ := c.central_D_structure H (reduced_kernel_sylow h) hb
    (c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hactor hcentral) ht htne
  have hrα : r∈Q F α := hDQ ⟨hr,hrt⟩
  have hrW : r∈centralizer (W:Set (G₀ L S)) := by
    intro w hw
    apply (G₀ L S).subtype_injective
    rw [map_mul,map_mul,hrx]
    apply hx.1.2
    change ι w∈(Z F u).map ι⊔(Z F (g • u)).map ι
    rw [←Subgroup.map_sup]
    exact mem_map_of_mem ι hw
  have hr1 : r≠1 := fun he => hx1 (by rw [←hrx,he,map_one])
  have hW' : W⊔Q F α=graphLocalGroup F α := by
    apply map_injective (G₀ L S).subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,hQam,reduced_graphLocalGroup_image h false]
    exact hW
  have hnt := residual_centralizer_not_transitive H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hab W hW' r hrα hr hrW hr1
  let C := (centralizer ({x}:Set G)).comap ι
  let A := (V F t 1⊓Q F α)⊓C
  let B := (V F y 1⊓Q F u)⊓C
  let A₀ := (V F t 1).map ι⊓Q₀
  let B₀ := (V F y 1).map ι⊓(Q F u).map ι
  have hmap (T : Subgroup (G₀ L S)) :
      (T⊓C).map ι=T.map ι⊓centralizer ({x}:Set G) := by
    ext z
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨mem_map_of_mem ι ha.1,ha.2⟩
    · rintro ⟨⟨a,ha,rfl⟩,hcx⟩
      exact mem_map.mpr ⟨a,⟨ha,hcx⟩,rfl⟩
  have hAm : A.map ι=A₀⊓centralizer ({x}:Set G) := by
    rw [show A=(V F t 1⊓Q F α)⊓C from rfl,hmap,
      map_inf _ _ _ (G₀ L S).subtype_injective,hQam]
  have hBm : B.map ι=B₀⊓centralizer ({x}:Set G) := by
    rw [show B=(V F y 1⊓Q F u)⊓C from rfl,hmap,
      map_inf _ _ _ (G₀ L S).subtype_injective]
  have htType : t.type=true := by
    have hh := ht.1
    change false≠t.type at hh
    cases hty : t.type with
    | false => exact (hh hty.symm).elim
    | true => rfl
  have huType : u.type=false := by
    have hh := hβu.1
    change true≠u.type at hh
    cases huy : u.type with
    | false => rfl
    | true => exact (hh huy.symm).elim
  have hyType : y.type=true := by
    have hh := hy.1
    rw [huType] at hh
    cases hyy : y.type with
    | false => exact (hh hyy.symm).elim
    | true => rfl
  have hVfinite (z : Vertex F) : Finite ((V F z 1).map ι) := by
    have hV : V F z 1≤stabilizer F z :=
      (graph_V_le_Q_of_short H (reduced_kernel_sylow h) z
        (by change 1 < b F; rw [hb]; decide)).trans (Q_le_stabilizer F z)
    let : Finite (V F z 1) := Finite.of_injective (inclusion hV) (inclusion_injective _)
    exact Finite.of_equiv (V F z 1)
      ((V F z 1).equivMapOfInjective ι (G₀ L S).subtype_injective).toEquiv
  let : Finite ((V F t 1).map ι) := hVfinite t
  let : Finite ((V F y 1).map ι) := hVfinite y
  let : Finite A₀ := Finite.of_injective (inclusion (show A₀≤(V F t 1).map ι from inf_le_left)) (inclusion_injective _)
  let : Finite B₀ := Finite.of_injective (inclusion (show B₀≤(V F y 1).map ι from inf_le_left)) (inclusion_injective _)
  have hct : (centralizer ({x}:Set G)).relIndex A₀≤2 :=
    (relIndex_le_of_le_right inf_le_left
      ((centralizer ({x}:Set G)).subgroupOf ((V F t 1).map ι)).index_ne_zero_of_finite).trans
      (hsmall t htType x hx.1.1.2)
  have hcy : (centralizer ({x}:Set G)).relIndex B₀≤2 :=
    (relIndex_le_of_le_right inf_le_left
      ((centralizer ({x}:Set G)).subgroupOf ((V F y 1).map ι)).index_ne_zero_of_finite).trans
      (hsmall y hyType x hx.2)
  obtain ⟨hAi,hBi⟩ := original_bTwo_opposite_radius_indices h hc hne hb hβu ht htne hy hyne e
  have hAc : Nat.card K≤2*(Q F β).relIndex A := by
    rw [←relIndex_map_map_of_injective (f:=ι) (Q F β) A (G₀ L S).subtype_injective,
      hQbm,hAm,←hAi]
    exact half_index_bound Q₁ A₀ (centralizer ({x}:Set G)) hct
  have hBc : Nat.card K≤2*(Q F β).relIndex B := by
    rw [←relIndex_map_map_of_injective (f:=ι) (Q F β) B (G₀ L S).subtype_injective,
      hQbm,hBm,←hBi]
    exact half_index_bound Q₁ B₀ (centralizer ({x}:Set G)) hcy
  have hCr : C≤centralizer ({r}:Set (G₀ L S)) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    apply (G₀ L S).subtype_injective
    rw [map_mul,map_mul,hrx]
    exact mem_centralizer_singleton_iff.mp ha
  have hdr : d∈centralizer ({r}:Set (G₀ L S)) := hCr hdcentral
  have hdfix : d • δ=δ := (ballKernel_le_stabilizer F δ 1) hdk
  have hau : α≠u := by
    intro he
    have hh := hc.1
    rw [←he,SimpleGraph.dist_self,hb] at hh
    contradiction
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hbound := cubic_centralizer_core_bound h hab.symm hβu hδ hau eβ hK A B
    (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right) hAc hBc r
    (inf_le_right.trans hCr) (inf_le_right.trans hCr) hnt d hd hdo hdr hdfix
  have hbound₀ : (Q F δ).map ι⊓centralizer ({x}:Set G)≤Q₁ := by
    intro z hz
    obtain ⟨z₀,hz₀,rfl⟩ := hz.1
    have hzC : z₀∈centralizer ({r}:Set (G₀ L S)) := hCr hz.2
    exact hQbm ▸ mem_map_of_mem ι (hbound ⟨hz₀,hzC⟩)
  have hmove : d • α≠α := by
    intro hfix
    have hh := cubic_centralizer_core_bound h hab.symm hβu hab.symm hau eβ hK A B
      (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right) hAc hBc r
      (inf_le_right.trans hCr) (inf_le_right.trans hCr) hnt d hd hdo hdr hfix
    have hAQ : A≤Q F β :=
      (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans hCr)).trans hh
    have hi : (Q F β).relIndex A=1 := relIndex_eq_one.mpr hAQ
    rw [hi,hK] at hAc
    omega
  refine ⟨hmove,hbound₀,?_,hact⟩
  intro hxδ
  obtain ⟨a,ha,haδ⟩ := graphLocalGroup_transitive H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) β ⟨α,hab.symm⟩ ⟨δ,hδ⟩
  change a • α=δ at haδ
  have haβ : a • β=β := sylowGenerated_le _ ha
  let ρ := a • t
  have hδρ : (graph F).Adj δ ρ := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F a).map_adj_iff.mpr ht
    change (graph F).Adj (a • α) (a • t) at hh
    rwa [haδ] at hh
  have hρType : ρ.type=true := by
    change t.type=true
    exact htType
  have hxρ : x∈(Q F ρ).map ι :=
    ((hact ρ hδρ).2 x hxδ (by
      have hc' : Commute x (ι d) := (mem_centralizer_singleton_iff.mp hdcentral).symm
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hc'.eq]
      exact one_mem _)).2
  let Aρ := (V F ρ 1).map ι⊓(Q F δ).map ι
  let : Finite ((V F ρ 1).map ι) := hVfinite ρ
  let : Finite Aρ := Finite.of_injective
    (inclusion (show Aρ≤(V F ρ 1).map ι from inf_le_left)) (inclusion_injective _)
  have hindex : Q₁.relIndex Aρ=4 := by
    have hi : (Q F β).relIndex (V F t 1⊓Q F α)=Nat.card K := by
      rw [←relIndex_map_map_of_injective (f:=ι) (Q F β) (V F t 1⊓Q F α)
        (G₀ L S).subtype_injective,hQbm,map_inf _ _ _ (G₀ L S).subtype_injective,hQam]
      exact hAi
    have hi' := relIndex_map_map_of_injective (f:=(MulAut.conj a).toMonoidHom)
      (Q F β) (V F t 1⊓Q F α) (MulAut.conj a).injective
    rw [←Q_translate,haβ,map_inf _ _ _ (MulAut.conj a).injective,
      ←V_translate,←Q_translate,haδ,hi,hK] at hi'
    rw [show Aρ=((V F ρ 1)⊓Q F δ).map ι from
      (map_inf _ _ _ (G₀ L S).subtype_injective).symm,←hQbm,
      relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
    exact hi'
  have hsmallρ : (centralizer ({x}:Set G)).relIndex Aρ≤2 :=
    (relIndex_le_of_le_right inf_le_left
      ((centralizer ({x}:Set G)).subgroupOf ((V F ρ 1).map ι)).index_ne_zero_of_finite).trans
      (hsmall ρ hρType x hxρ)
  have hhalf := half_index_bound Q₁ Aρ (centralizer ({x}:Set G)) hsmallρ
  have htrivial : Q₁.relIndex (Aρ⊓centralizer ({x}:Set G))=1 :=
    relIndex_eq_one.mpr ((inf_le_inf_right _ inf_le_right).trans hbound₀)
  rw [hindex,htrivial] at hhalf
  omega

/-- The original third-root interface, retaining the original witness and
all original quotient and inclusion maps. -/
theorem original_bTwo_field_four_terminal_third_root
    {K₀ : Type*} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F (base F false) u)
    (hne : ⁅Z F (base F false),Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj (base F true) u)
    (ht : (graph F).Adj (base F false) t) (htne : t≠base F true)
    (e₀ : (L 0⧸pCore 2 (L 0))≃*PSL(2,K₀)) (hK₀ : Nat.card K₀=2)
    (e : (L 1⧸pCore 2 (L 1))≃*PSL(2,K))
    (hK : Nat.card K=4)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map (G₀ L S).subtype≠
      (Z F (base F false)).map (G₀ L S).subtype) :
    ∃ g∈graphLocalGroup F (base F false), g • base F true=t ∧
      let ι := (G₀ L S).subtype
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      W₀⊔Q₀=enlargedEndpoint L S 0 ∧
      R₀=(D₀⊓(Q F u).map ι)⊓(Q F (g • u)).map ι ∧ R₀≠⊥ ∧
      ∀ y : Vertex F, (graph F).Adj u y → y≠base F true →
        ∀ x∈R₀⊓(Q F y).map ι, x≠1 →
          ∃ d∈graphLocalGroup F (base F true), orderOf d=3 ∧ orderOf (ι d)=3 ∧
            ι d∈(((V F t 1).map ι⊓Q₀)⊓centralizer ({x}:Set G))⊔
              (((V F y 1).map ι⊓(Q F u).map ι)⊓centralizer ({x}:Set G)) ∧
            ι d∈centralizer ({x}:Set G) ∧
            ∃ δ : Vertex F, (graph F).Adj (base F true) δ ∧
              δ≠base F false ∧ d∈ballKernel F δ 1 ∧
              ((Q F δ).map ι⊓centralizer ({x}:Set G)≤Q₁) ∧
              x∉(Q F δ).map ι ∧
              ∀ ρ : Vertex F, (graph F).Adj δ ρ →
                d∈graphLocalGroup F ρ ∧
                  ∀ z∈(Q F δ).map ι, ⁅z,ι d⁆∈Q₁⊓(Q F ρ).map ι →
                    z∈Q₁⊓(Q F ρ).map ι := by
  obtain ⟨g,hg,hgt,hW,hfour,hR,hcubic⟩ :=
    original_bTwo_field_four_terminal_third_root_moving h hc hne hb hβu ht htne e₀ hK₀ e hK hD
  refine ⟨g,hg,hgt,hW,hfour,hR,?_⟩
  intro y hy hyne x hx hxne
  obtain ⟨d,hd,ho,hoι,hr,hc,δ,hδ,hδα,hdk,_,hbound,hout,hact⟩ :=
    hcubic y hy hyne x hx hxne
  exact ⟨d,hd,ho,hoι,hr,hc,δ,hδ,hδα,hdk,hbound,hout,hact⟩

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
