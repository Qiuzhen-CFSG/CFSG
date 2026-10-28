module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.ActorCentralizers.Geometry
/-!
# Sylow control and weak closure in C(a)

Under contrary actor nonfusion, a normalizer of the local order-32 group
must fix z: z is its unique nonidentity central element in E, and all
outside involutions in N(E) are fused to d. The p-group normalizer condition
therefore proves Sylow maximality in C(a). The A6 quotient makes
C(a) ∩ N(E) a two-group, so it equals this local group.

If a conjugate of z under C(a) returns to that Sylow subgroup, its full
centralizer lies in N(E). It thus conjugates the local group into itself;
finiteness makes this equality, and normalizer control fixes z. This proves
weak closure with respect to the whole C(a).

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 7 and the C(a) analysis on pp.6–7.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

public theorem actorLocalCentralizer_normalizer_control (hE : ENormalizerAction D k)
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
  have hyE := marked_conjugate_mem_E D k hE hn
    (actorLocalCentralizer_le_normalizer_E D k (f zU).property) hzy
  have hyne : ((f zU : U) : G) ≠ 1 := by
    intro h
    have h1 : f zU = 1 := Subtype.ext h
    exact D.z_ne_one (congrArg Subtype.val (f.injective (h1.trans f.map_one.symm)))
  have hyz : ((f zU : U) : G) = D.z :=
    (actorLocalCentralizer_center_E D k (f zU).property hyE
      (fun y hy => congrArg Subtype.val (mem_center_iff.mp hfC ⟨y, hy⟩))).resolve_left hyne
  exact ⟨hnU.2, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hyz)⟩

public theorem actorLocalCentralizer_maximal_two (hE : ENormalizerAction D k)
    (hn : ¬ IsConj D.z (into D k d)) (V : Subgroup G) (hV : IsPGroup 2 V)
    (hUV : actorLocalCentralizer D k ≤ V)
    (hVH : V ≤ centralizer ({into D k a} : Set G)) : V = actorLocalCentralizer D k := by
  let U := actorLocalCentralizer D k
  let : Group.IsNilpotent V := hV.isNilpotent
  have hself : normalizer (U.subgroupOf V : Set V) = U.subgroupOf V := by
    apply le_antisymm _ le_normalizer
    rw [← subgroupOf_normalizer_eq hUV]
    intro x hx
    exact actorLocalCentralizer_normalizer_control D k hE hn ⟨hx, hVH x.property⟩
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := V)) _ hself
  exact le_antisymm (subgroupOf_eq_top.mp htop) hUV

omit [Finite G] in
public theorem actor_normalizer_centralizer_isPGroup (hE : ENormalizerAction D k) :
    IsPGroup 2 ↥(centralizer ({into D k a} : Set G) ⊓ normalizer (E D k : Set G)) := by
  let N := normalizer (E D k : Set G)
  let B := (E D k).subgroupOf N
  let aN : N := ⟨into D k a, centralizer_le_normalizer_E D k (k a).property⟩
  obtain ⟨e⟩ := hE.quotient
  let q : N →* alternatingGroup (Fin 6) := e.toMonoidHom.comp (QuotientGroup.mk' B)
  have hqa : orderOf (q aN) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      have ha2 : aN ^ 2 = 1 := by
        apply Subtype.ext
        change (into D k a) ^ 2 = 1
        rw [← map_pow, show a ^ 2 = 1 from by simpa only [actor_orders.1] using pow_orderOf_eq_one a, map_one]
      rw [ha2, map_one]
    · intro h
      have haB : aN ∈ B := (QuotientGroup.eq_one_iff aN).mp
        (e.injective (h.trans e.map_one.symm))
      have haE : into D k a ∈ E D k := haB
      rw [← modelE_map D k, mem_map_iff_mem (into_injective D k)] at haE
      have hna : a ∉ modelE := by change a.right ≠ 1; decide +kernel
      exact hna haE
  have hker : IsPGroup 2 q.ker := by
    have heq : q.ker = B := by
      ext x
      change e (QuotientGroup.mk' B x) = 1 ↔ x ∈ B
      rw [← e.map_one, e.injective.eq_iff]
      exact QuotientGroup.eq_one_iff x
    rw [heq]
    let := E_elementary D k
    exact (IsElementaryAbelian.isPGroup 2 (E D k)).comap_subtype
  have hp := (alternatingGroup.isPGroup_centralizer_involution_of_degree_le_six
    (by rfl) (q aN) hqa).comap_of_ker_isPGroup q hker
  have hinc : centralizer ({aN} : Set N) ≤ (centralizer ({q aN} : Set _)).comap q := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (by simpa only [map_mul] using congrArg q (mem_centralizer_singleton_iff.mp hx))
  have hmap := (hp.to_le hinc).map N.subtype
  have heq : (centralizer ({aN} : Set N)).map N.subtype =
      centralizer ({into D k a} : Set G) ⊓ N := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)), x.property⟩
    · intro x hx
      exact ⟨⟨x, hx.2⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hx.1)), rfl⟩
  rwa [heq] at hmap

public theorem actor_normalizer_centralizer_eq (hE : ENormalizerAction D k)
    (hn : ¬ IsConj D.z (into D k d)) :
    centralizer ({into D k a} : Set G) ⊓ normalizer (E D k : Set G) =
      actorLocalCentralizer D k := by
  exact actorLocalCentralizer_maximal_two D k hE hn _
    (actor_normalizer_centralizer_isPGroup D k hE)
    (le_inf inf_le_left (actorLocalCentralizer_le_normalizer_E D k)) inf_le_left

public theorem actorLocalCentralizer_weakly_closed (hE : ENormalizerAction D k)
    (hn : ¬ IsConj D.z (into D k d)) (g : G)
    (hg : g ∈ centralizer ({into D k a} : Set G))
    (hgz : g * D.z * g⁻¹ ∈ actorLocalCentralizer D k) : g * D.z * g⁻¹ = D.z := by
  let U := actorLocalCentralizer D k
  let f := MulAut.conj g
  have hyE := marked_conjugate_mem_E D k hE hn
    (actorLocalCentralizer_le_normalizer_E D k hgz) (isConj_iff.mpr ⟨g, rfl⟩)
  have hyne : g * D.z * g⁻¹ ≠ 1 := by
    intro h
    exact D.z_ne_one (f.injective (h.trans f.map_one.symm))
  have hCU := E_element_centralizer_le_normalizer D k hE _ hyE hyne
  have hmap : U.map f.toMonoidHom ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    change f x ∈ actorLocalCentralizer D k
    rw [← actor_normalizer_centralizer_eq D k hE hn]
    have hgfix : f (into D k a) = into D k a := by
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg)
    refine ⟨mem_centralizer_singleton_iff.mpr ?_, hCU ?_⟩
    · simpa only [map_mul, hgfix] using congrArg f (mem_centralizer_singleton_iff.mp hx.1)
    · exact mem_centralizer_singleton_iff.mpr
        (by
          change f x * f D.z = f D.z * f x
          simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hx.2))
  have heq : U.map f.toMonoidHom = U :=
    eq_of_le_of_card_ge hmap (by rw [card_map_of_injective f.injective])
  have hgU : g ∈ normalizer (U : Set G) := mem_normalizer_iff_map_conj_eq.mpr heq
  have hgC := (actorLocalCentralizer_normalizer_control D k hE hn ⟨hgU, hg⟩).2
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hgC)

public theorem actorLocalCentralizer_sylow (hE : ENormalizerAction D k)
    (hn : ¬ IsConj D.z (into D k d)) :
    ∃ S : Sylow 2 (centralizer ({into D k a} : Set G)),
      (S : Subgroup _) = (actorLocalCentralizer D k).subgroupOf
        (centralizer ({into D k a} : Set G)) := by
  let H := centralizer ({into D k a} : Set G)
  let U := actorLocalCentralizer D k
  have hUH : U ≤ H := inf_le_left
  obtain ⟨S, hUS⟩ := ((actorLocalCentralizer_isPGroup D k).comap_subtype (K := H)).exists_le_sylow
  have heq : (S : Subgroup H).map H.subtype = U :=
    actorLocalCentralizer_maximal_two D k hE hn _ (S.isPGroup'.map H.subtype)
      (by change U ≤ _; rw [← map_subgroupOf_eq_of_le hUH]; exact map_mono hUS) (map_subtype_le _)
  refine ⟨S, le_antisymm ?_ hUS⟩
  intro x hx
  change (x : G) ∈ U
  exact heq ▸ mem_map_of_mem H.subtype hx

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
