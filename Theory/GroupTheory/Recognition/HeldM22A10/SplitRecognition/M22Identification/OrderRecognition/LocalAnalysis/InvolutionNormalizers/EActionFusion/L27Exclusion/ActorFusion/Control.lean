module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.ActorFusion.LocalCore
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.ActorCentralizers.Geometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.InitialFusion.ActorFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.QuotientAlternatives.OrbitReduction

/-!
# Local Sylow control in the order-168 branch

Under contrary actor nonfusion, a conjugate of z in the local two-group
U = C(a) ∩ C(z) lies in E. Its unique nonidentity central point in E
forces N_{C(a)}(U) = U. The p-group normalizer condition makes U Sylow
in C(a), without any quotient-recognition premise.

If C(a) ∩ N(E) is a two-group, it therefore equals U. Fusion of printed
z₁ and z₃ gives C(z₃) ≤ N(E), discharging the remaining intersection
premise of the local core-free Z-star proof. Actual conjugacy of d and a
in N(E) then transports centralizer containment to C(d). Finally, the
five local involution classes reduce full centralizer closure of N(E)
to the separate bound for C(z₂).

The two-group and d-to-a conjugacy conditions are explicit finite-action
inputs; no A6 quotient or transitivity on all of E is assumed.
Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, printed pp.6–7.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

private theorem marked_conjugate_in_local_mem_E
    (hn : ¬ IsConj D.z (into D k d)) (x : G)
    (hxU : x ∈ actorLocalCentralizer D k) (hconj : IsConj D.z x) : x ∈ E D k := by
  let v := k.symm ⟨x, hxU.2⟩
  have hv : into D k v = x := congrArg Subtype.val (k.apply_symm_apply _)
  have hv2 : orderOf v = 2 := by
    rw [← orderOf_injective (into D k) (into_injective D k), hv]
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← hg, ← MulAut.conj_apply, MulEquiv.orderOf_eq, D.z_order]
  have hvE (i : Fin 4) (h : IsConj v (z i)) : x ∈ E D k := by
    have hh := (SemidirectProduct.rightHom : TwistedModel →* SymmetricFour).map_isConj h
    change IsConj v.right (z i).right at hh
    rw [show (z i).right = 1 from z_mem_modelE i] at hh
    rw [← hv, ← modelE_map D k]
    exact mem_map_of_mem _ (isConj_one_left.mp hh)
  rcases model_involution_classes v hv2 with h | h | h | h | h
  · exact hvE 0 h
  · exact hvE 1 h
  · exact hvE 2 h
  · exact False.elim (hn (actor_fusion_of_a D k
      (hconj.trans (hv ▸ (into D k).map_isConj h))))
  · exact False.elim (hn (hconj.trans (hv ▸ (into D k).map_isConj h)))

public theorem l27_actorLocalCentralizer_normalizer_control
    (hn : ¬ IsConj D.z (into D k d)) :
    normalizer (actorLocalCentralizer D k : Set G) ⊓ centralizer ({into D k a} : Set G) ≤
      actorLocalCentralizer D k := by
  intro n hnU
  let U := actorLocalCentralizer D k
  let zU : U := ⟨D.z, actorLocalCentralizer_z_mem D k⟩
  have hzC : zU ∈ center U := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2)
  let f := U.normalizerMonoidHom ⟨n, hnU.1⟩
  have hfC : f zU ∈ center U := characteristic_iff_le_comap.mp inferInstance f hzC
  have hzy : IsConj D.z ((f zU : U) : G) := isConj_iff.mpr ⟨n, rfl⟩
  have hyE := marked_conjugate_in_local_mem_E D k hn _ (f zU).property hzy
  have hyne : ((f zU : U) : G) ≠ 1 := by
    intro h
    have h1 : f zU = 1 := Subtype.ext h
    exact D.z_ne_one (congrArg Subtype.val (f.injective (h1.trans f.map_one.symm)))
  have hyz : ((f zU : U) : G) = D.z :=
    (actorLocalCentralizer_center_E D k (f zU).property hyE
      (fun y hy => congrArg Subtype.val (mem_center_iff.mp hfC ⟨y, hy⟩))).resolve_left hyne
  exact ⟨hnU.2, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hyz)⟩

public theorem l27_actorLocalCentralizer_maximal_two
    (hn : ¬ IsConj D.z (into D k d)) (V : Subgroup G) (hV : IsPGroup 2 V)
    (hUV : actorLocalCentralizer D k ≤ V)
    (hVH : V ≤ centralizer ({into D k a} : Set G)) : V = actorLocalCentralizer D k := by
  let U := actorLocalCentralizer D k
  let : Group.IsNilpotent V := hV.isNilpotent
  have hself : normalizer (U.subgroupOf V : Set V) = U.subgroupOf V := by
    apply le_antisymm _ le_normalizer
    rw [← subgroupOf_normalizer_eq hUV]
    intro x hx
    exact l27_actorLocalCentralizer_normalizer_control D k hn ⟨hx, hVH x.property⟩
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := V)) _ hself
  exact le_antisymm (subgroupOf_eq_top.mp htop) hUV

public theorem l27_actorLocalCentralizer_sylow
    (hn : ¬ IsConj D.z (into D k d)) :
    ∃ S : Sylow 2 (centralizer ({into D k a} : Set G)),
      (S : Subgroup _) = (actorLocalCentralizer D k).subgroupOf
        (centralizer ({into D k a} : Set G)) := by
  let H := centralizer ({into D k a} : Set G)
  let U := actorLocalCentralizer D k
  have hUH : U ≤ H := inf_le_left
  obtain ⟨S, hUS⟩ := ((actorLocalCentralizer_isPGroup D k).comap_subtype (K := H)).exists_le_sylow
  have heq : (S : Subgroup H).map H.subtype = U :=
    l27_actorLocalCentralizer_maximal_two D k hn _ (S.isPGroup'.map H.subtype)
      (by change U ≤ _; rw [← map_subgroupOf_eq_of_le hUH]; exact map_mono hUS) (map_subtype_le _)
  refine ⟨S, le_antisymm ?_ hUS⟩
  intro x hx
  change (x : G) ∈ U
  exact heq ▸ mem_map_of_mem H.subtype hx

omit [Finite G] in
private theorem centralizer_le_of_normalizer_conjugate (N : Subgroup G) {s t : G}
    (n : N) (hn : (n : G) * s * (n : G)⁻¹ = t)
    (ht : centralizer ({t} : Set G) ≤ N) : centralizer ({s} : Set G) ≤ N := by
  intro x hx
  have hxc : (n : G) * x * (n : G)⁻¹ ∈ centralizer ({t} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hn]
    simpa only [map_mul, MulAut.conj_apply] using congrArg (MulAut.conj (n : G))
      (mem_centralizer_singleton_iff.mp hx)
  have hmem := N.mul_mem (N.mul_mem (N.inv_mem n.property) (ht hxc)) n.property
  simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hmem

/-- Every marked conjugate in E has its full centralizer inside N(E). -/
public theorem l27_marked_conjugate_centralizer_le_normalizer
    (x : E D k) (hx : IsConj D.z (x : G)) :
    centralizer ({(x : G)} : Set G) ≤ normalizer (E D k : Set G) := by
  obtain ⟨n, hn⟩ := E_normalizer_fusion_of_isConj D k x hx
  apply centralizer_le_of_normalizer_conjugate _ n⁻¹ _ (centralizer_le_normalizer_E D k)
  change (n : G)⁻¹ * (x : G) * ((n : G)⁻¹)⁻¹ = D.z
  rw [← hn]
  group

/-- The finite normalizer-centralizer condition discharges the intersection
premise of the core-free Z-star argument inside C(a). -/
public theorem l27_a_centralizer_le_marked_of_normalizer_two_group
    (hz3 : IsConj D.z (into D k (z 2)))
    (hn : ¬ IsConj D.z (into D k d))
    (hp : IsPGroup 2 ↥(centralizer ({into D k a} : Set G) ⊓
      normalizer (E D k : Set G))) :
    centralizer ({into D k a} : Set G) ≤ D.centralizer := by
  have hlocal : centralizer ({into D k a} : Set G) ⊓ normalizer (E D k : Set G) =
      actorLocalCentralizer D k :=
    l27_actorLocalCentralizer_maximal_two D k hn _ hp
      (le_inf inf_le_left (actorLocalCentralizer_le_normalizer_E D k)) inf_le_left
  apply l27_a_centralizer_le_marked_of_local_sylow D k hz3
    (fun h => hn (actor_fusion_of_a D k h)) hn
  · obtain ⟨S, hS⟩ := l27_actorLocalCentralizer_sylow D k hn
    refine ⟨S, hS.trans ?_⟩
    ext x
    exact ⟨fun h => h.2, fun h => ⟨x.property, h⟩⟩
  · have hC := l27_marked_conjugate_centralizer_le_normalizer D k
      ⟨into D k (z 2), modelE_map D k ▸ mem_map_of_mem _ (z_mem_modelE 2)⟩ hz3
    intro x hx
    exact (hlocal ▸ (show x ∈ centralizer ({into D k a} : Set G) ⊓
      normalizer (E D k : Set G) from ⟨hx.2, hC hx.1⟩)).2

omit [Finite G] in
/-- Actual d-to-a fusion inside N(E) transports the full centralizer bound. -/
public theorem l27_d_centralizer_le_normalizer_of_actor_control
    (ha : centralizer ({into D k a} : Set G) ≤ D.centralizer)
    (hda : ∃ n : normalizer (E D k : Set G),
      (n : G) * into D k d * (n : G)⁻¹ = into D k a) :
    centralizer ({into D k d} : Set G) ≤ normalizer (E D k : Set G) := by
  obtain ⟨n, hn⟩ := hda
  exact centralizer_le_of_normalizer_conjugate _ n hn
    (ha.trans (centralizer_le_normalizer_E D k))

/-- The five actual local involution classes suffice for centralizer closure
in N(E). Conjugators into the Sylow subgroup are chosen inside N(E). -/
public theorem l27_E_centralizer_closure_of_representatives
    (hz3 : IsConj D.z (into D k (z 2)))
    (hC1 : centralizer ({into D k (z 1)} : Set G) ≤ normalizer (E D k : Set G))
    (ha : centralizer ({into D k a} : Set G) ≤ normalizer (E D k : Set G))
    (hd : centralizer ({into D k d} : Set G) ≤ normalizer (E D k : Set G)) :
    ∀ t ∈ normalizer (E D k : Set G), orderOf t = 2 →
      centralizer ({t} : Set G) ≤ normalizer (E D k : Set G) := by
  let N := normalizer (E D k : Set G)
  have hSN : (D.sylow : Subgroup G) ≤ N :=
    D.sylow_le_centralizer.trans (centralizer_le_normalizer_E D k)
  let S : Sylow 2 N := D.sylow.subtype hSN
  intro t htN ht
  let tN : N := ⟨t, htN⟩
  have ht2 : orderOf tN = 2 := (Subgroup.orderOf_coe tN).symm.trans ht
  have hp : IsPGroup 2 (zpowers tN) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using ht2)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N T S
  have hyS : (MulAut.conj n) tN ∈ (S : Subgroup N) := by
    rw [← hn]
    exact mem_map_of_mem (MulAut.conj n).toMonoidHom (hT (mem_zpowers tN))
  let y : G := ((MulAut.conj n) tN : N)
  have hyC : y ∈ D.centralizer := D.sylow_le_centralizer hyS
  let v := k.symm ⟨y, hyC⟩
  have hv : into D k v = y := congrArg Subtype.val (k.apply_symm_apply _)
  have hv2 : orderOf v = 2 := by
    rw [← orderOf_injective (into D k) (into_injective D k), hv]
    change orderOf ((MulAut.conj (n : G)) t) = 2
    rw [MulEquiv.orderOf_eq, ht]
  have transport (r : TwistedModel) (hc : IsConj v r)
      (hCr : centralizer ({into D k r} : Set G) ≤ N) :
      centralizer ({into D k v} : Set G) ≤ N := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    apply centralizer_le_of_normalizer_conjugate N
      ⟨into D k c, centralizer_le_normalizer_E D k (k c).property⟩ _ hCr
    simpa only [map_mul, map_inv] using congrArg (into D k) hc
  have hCv : centralizer ({into D k v} : Set G) ≤ N := by
    rcases model_involution_classes v hv2 with h | h | h | h | h
    · apply transport _ h
      rw [into_z_zero D k]
      exact centralizer_le_normalizer_E D k
    · exact transport _ h hC1
    · exact transport _ h (l27_marked_conjugate_centralizer_le_normalizer D k
        ⟨into D k (z 2), modelE_map D k ▸ mem_map_of_mem _ (z_mem_modelE 2)⟩ hz3)
    · exact transport _ h ha
    · exact transport _ h hd
  exact centralizer_le_of_normalizer_conjugate N n hv.symm hCv

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
