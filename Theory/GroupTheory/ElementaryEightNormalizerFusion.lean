module

public import Theory.GroupTheory.ElementaryEightSylowFour
public import Mathlib.GroupTheory.Sylow

/-!
# Fusion obstruction from elementary-eight normalizers

Suppose every elementary subgroup of order eight in a Sylow two-subgroup
is self-centralizing and has normalizer of order 32. A central Sylow
involution cannot fuse to an involution with elementary centralizer of
order eight. Conjugacy produces a second Sylow subgroup centralizing that
involution. The two local normalizer images in the elementary-eight
automizer both have order four; the uniform normalizer bound makes these
Sylow subgroups. The small-automizer theorem identifies both with the
two-core. This would make the first normalizer centralize the outside
involution, contradicting the orders 32 and eight.

This strengthens the local argument in `ElementaryEightCentralizerFusionObstruction`
by deriving the needed automizer solvability from its Sylow order, and
replacing saturation by the uniform self-centralizer condition. Source
context: MacWilliams, Trans. AMS 150 (1970), DOI
10.1090/S0002-9947-1970-0276324-3; Janko–Thompson, Math. Z. 113 (1970),
Theorem 1.3 and the elementary-eight normalizer arguments in Section 4.
-/

open Subgroup

private theorem four_subgroups_eq
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (A : Subgroup (MulAut E))
    (hbound : ∀ P : Sylow 2 A, Nat.card P ≤ 4)
    (B D : Subgroup A) (hB : Nat.card B = 4) (hD : Nat.card D = 4) : B = D := by
  have heq (K : Subgroup A) (hK : Nat.card K = 4) : K = pCore 2 A := by
    have hp : IsPGroup 2 K := IsPGroup.of_card (n := 2) (by simpa using hK)
    obtain ⟨P, hKP⟩ := hp.exists_le_sylow
    have hKPeq : K = (P : Subgroup A) := eq_of_le_of_card_ge hKP (by rw [hK]; exact hbound P)
    have hP : Nat.card P = 4 := by rw [← hKPeq]; exact hK
    exact hKPeq.trans (sylow_eq_pCore_of_elementary_eight_automorphisms_sylow_four E hE A P hP)
  exact (heq B hB).trans (heq D hD).symm


private theorem normalizer_images_eq
    {G : Type*} [Group G] [Finite G] (U : Subgroup G)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (hbound : ∀ P : Sylow 2 (normalizer (U : Set G)), Nat.card P ≤ 32)
    (R Q : Subgroup (normalizer (U : Set G)))
    (hR : Nat.card R = 32) (hQ : Nat.card Q = 32)
    (hCR : Nat.card (U.normalizerMonoidHom.ker.subgroupOf R) = 8)
    (hCQ : Nat.card (U.normalizerMonoidHom.ker.subgroupOf Q) = 8) :
    R.map U.normalizerMonoidHom = Q.map U.normalizerMonoidHom := by
  let N := normalizer (U : Set G)
  let f := U.normalizerMonoidHom.rangeRestrict
  let A := U.normalizerMonoidHom.range
  let UN := U.subgroupOf N
  have hUN : Nat.card UN = 8 := (Nat.card_congr (subgroupOfEquivOfLe U.le_normalizer).toEquiv).trans hU
  let : IsElementaryAbelian 2 UN := IsElementaryAbelian.subgroupOf U.le_normalizer
  have hUK : UN ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict, normalizerMonoidHom_ker]
    exact comap_mono U.le_centralizer
  have hA (P : Sylow 2 A) : Nat.card P ≤ 4 := by
    obtain ⟨T, rfl⟩ := Sylow.mapSurjective_surjective U.normalizerMonoidHom.rangeRestrict_surjective 2 P
    have hUT : UN ≤ T := (IsElementaryAbelian.isPGroup 2 UN).le_sylow_of_normal T
    have hsub : 8 ≤ Nat.card (f.ker.subgroupOf (T : Subgroup N)) := by
      have hh := card_le_of_le (comap_mono (f := (T : Subgroup N).subtype) hUK)
      rw [← subgroupOf, Nat.card_congr (subgroupOfEquivOfLe hUT).toEquiv, hUN] at hh
      exact hh
    have hmul := (f.ker.subgroupOf (T : Subgroup N)).card_mul_index
    rw [show (f.ker.subgroupOf (T : Subgroup N)).index = Nat.card ((T : Subgroup N).map f) from
      relIndex_ker (T : Subgroup N) f] at hmul
    have hT := hbound T
    change Nat.card ((T : Subgroup N).map f) ≤ 4
    nlinarith
  have image_card (K : Subgroup N) (hK : Nat.card K = 32)
      (hCK : Nat.card (U.normalizerMonoidHom.ker.subgroupOf K) = 8) :
      Nat.card (K.map f) = 4 := by
    have hmul := (f.ker.subgroupOf K).card_mul_index
    rw [MonoidHom.ker_rangeRestrict, hCK, hK] at hmul
    have hi := relIndex_ker K f
    change (f.ker.subgroupOf K).index = _ at hi
    rw [MonoidHom.ker_rangeRestrict] at hi
    rw [hi] at hmul
    omega
  have heq := four_subgroups_eq hU A hA (R.map f) (Q.map f)
    (image_card R hR hCR) (image_card Q hQ hCQ)
  have hh := congrArg (Subgroup.map A.subtype) heq
  simpa only [map_map, A, f, MonoidHom.subtype_comp_rangeRestrict] using hh

private theorem normalizer_card_transport
    {G : Type*} [Group G] [Finite G] (S T : Sylow 2 G)
    (hcount : ∀ F : Subgroup S, IsElementaryAbelian 2 F → Nat.card F = 8 →
      Nat.card (normalizer (F : Set S)) = 32)
    (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (hUT : U ≤ T) : Nat.card ((normalizer (U : Set G)).subgroupOf (T : Subgroup G)) = 32 := by
  let F := U.subgroupOf (T : Subgroup G)
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hUT
  let e := T.equiv S
  let : IsElementaryAbelian 2 (F.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hF : Nat.card (F.map e.toMonoidHom) = 8 := by
    rw [card_map_of_injective e.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe hUT).toEquiv).trans hU
  have hh := hcount (F.map e.toMonoidHom) inferInstance hF
  rw [← map_equiv_normalizer_eq, card_map_of_injective e.injective] at hh
  rw [subgroupOf_normalizer_eq hUT]
  exact hh

private theorem psubgroup_normalizer_card_bound
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hcount : ∀ F : Subgroup S, IsElementaryAbelian 2 F → Nat.card F = 8 →
      Nat.card (normalizer (F : Set S)) = 32)
    (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (P : Subgroup G) (hp : IsPGroup 2 P) (hUP : U ≤ P)
    (hPN : P ≤ normalizer (U : Set G)) : Nat.card P ≤ 32 := by
  obtain ⟨T, hPT⟩ := hp.exists_le_sylow
  have hh := card_le_of_le (comap_mono (f := (T : Subgroup G).subtype) hPN)
  change Nat.card (P.subgroupOf (T : Subgroup G)) ≤
    Nat.card ((normalizer (U : Set G)).subgroupOf (T : Subgroup G)) at hh
  rw [Nat.card_congr (subgroupOfEquivOfLe hPT).toEquiv,
    normalizer_card_transport S T hcount U hU (hUP.trans hPT)] at hh
  exact hh

private theorem normalizer_sylow_card_bound
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hcount : ∀ F : Subgroup S, IsElementaryAbelian 2 F → Nat.card F = 8 →
      Nat.card (normalizer (F : Set S)) = 32)
    (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (P : Sylow 2 (normalizer (U : Set G))) : Nat.card P ≤ 32 := by
  let N := normalizer (U : Set G)
  let UN := U.subgroupOf N
  let : IsElementaryAbelian 2 UN := IsElementaryAbelian.subgroupOf U.le_normalizer
  have hUP : UN ≤ P := (IsElementaryAbelian.isPGroup 2 UN).le_sylow_of_normal P
  have hm : U ≤ (P : Subgroup N).map N.subtype := by
    rintro u hu
    exact ⟨⟨u, U.le_normalizer hu⟩, hUP hu, rfl⟩
  have hh := psubgroup_normalizer_card_bound S hcount U hU
    ((P : Subgroup N).map N.subtype) (P.isPGroup'.map N.subtype) hm (map_subtype_le _)
  rwa [card_map_of_injective N.subtype_injective] at hh

private theorem exists_centralizing_sylow
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (z : S) (hz : z ∈ center S) (t : G) (hconj : IsConj (z : G) t)
    (U : Subgroup G) (hUp : IsPGroup 2 U) (hUC : U ≤ centralizer ({t} : Set G)) :
    ∃ T : Sylow 2 G, U ≤ T ∧ (T : Subgroup G) ≤ centralizer ({t} : Set G) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let a := MulAut.conj g
  let R := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let C := centralizer ({t} : Set G)
  have hRC : (R : Subgroup G) ≤ C := by
    rintro _ ⟨s, hs, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hcomm : (z : G) * s = s * z :=
      (congrArg Subtype.val (mem_center_iff.mp hz (⟨s, hs⟩ : S))).symm
    change a s * t = t * a s
    have ha : a (z : G) = t := hg
    rw [← ha, ← map_mul, ← map_mul, hcomm]
  obtain ⟨Q, hUQ⟩ := (hUp.comap_subtype (K := C)).exists_le_sylow
  let I := (Q : Subgroup C).map C.subtype
  have hUI : U ≤ I := by
    intro u hu
    exact ⟨⟨u, hUC hu⟩, hUQ hu, rfl⟩
  have hIcard : Nat.card I = Nat.card R := by
    rw [card_map_of_injective C.subtype_injective,
      Nat.card_congr (Q.equiv (R.subtype hRC)).toEquiv]
    exact Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv
  obtain ⟨T, hIT⟩ := (Q.isPGroup'.map C.subtype).exists_le_sylow
  have hITeq : I = (T : Subgroup G) := eq_of_le_of_card_ge hIT (by
    rw [hIcard, Nat.card_congr (R.equiv T).toEquiv])
  exact ⟨T, hITeq ▸ hUI, hITeq ▸ map_subtype_le (Q : Subgroup C)⟩

private theorem normalizer_kernel_card
    {G : Type*} [Group G] [Finite G] (U R : Subgroup G)
    (hRN : R ≤ normalizer (U : Set G)) (hCR : R ⊓ centralizer (U : Set G) = U) :
    Nat.card (U.normalizerMonoidHom.ker.subgroupOf
      (R.subgroupOf (normalizer (U : Set G)))) = Nat.card U := by
  let N := normalizer (U : Set G)
  let RN := R.subgroupOf N
  let K := U.normalizerMonoidHom.ker.subgroupOf RN
  have hUR : U ≤ R := hCR.symm.le.trans inf_le_left
  have hUC : U ≤ centralizer (U : Set G) := hCR.symm.le.trans inf_le_right
  let e : K ≃* U :=
    { toFun := fun k => ⟨k.val.val.val, by
        have hc : k.val.val.val ∈ centralizer (U : Set G) := by
          have hk := k.property
          change k.val.val ∈ U.normalizerMonoidHom.ker at hk
          rw [normalizerMonoidHom_ker] at hk
          exact hk
        exact hCR.le ⟨k.val.property, hc⟩⟩
      invFun := fun u => ⟨⟨⟨u, hRN (hUR u.property)⟩, hUR u.property⟩, by
        change (⟨u, hRN (hUR u.property)⟩ : N) ∈ U.normalizerMonoidHom.ker
        rw [normalizerMonoidHom_ker]
        exact hUC u.property⟩
      left_inv := by intro k; rfl
      right_inv := by intro u; rfl
      map_mul' := by intros; rfl }
  exact Nat.card_congr e.toEquiv

private theorem self_centralizer_in_psubgroup
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hself : ∀ F : Subgroup S, IsElementaryAbelian 2 F → Nat.card F = 8 →
      centralizer (F : Set S) = F)
    (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (P : Subgroup G) (hp : IsPGroup 2 P) (hUP : U ≤ P) :
    P ⊓ centralizer (U : Set G) = U := by
  obtain ⟨T, hPT⟩ := hp.exists_le_sylow
  let F := U.subgroupOf (T : Subgroup G)
  have hUT : U ≤ T := hUP.trans hPT
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hUT
  let e := T.equiv S
  let D := F.map e.toMonoidHom
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map _
  have hD : Nat.card D = 8 := by
    rw [card_map_of_injective e.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe hUT).toEquiv).trans hU
  have hDC := hself D inferInstance hD
  apply le_antisymm ?_ (le_inf hUP U.le_centralizer)
  intro p hp
  let pT : T := ⟨p, hPT hp.1⟩
  have hm : e pT ∈ centralizer (D : Set S) := by
    rintro _ ⟨u, hu, rfl⟩
    have hc : u * pT = pT * u := Subtype.ext (hp.2 u hu)
    change e u * e pT = e pT * e u
    simpa only [map_mul] using congrArg e hc
  rw [hDC] at hm
  obtain ⟨u, hu, he⟩ := hm
  have he' : u = pT := e.injective he
  change (pT : G) ∈ U
  rw [← he']
  exact hu

/-- Uniform self-centralizers and order-32 normalizers exclude fusion of
a central Sylow involution to one with an elementary-eight centralizer. -/
public theorem Sylow.not_isConj_of_elementary_eight_centralizer_geometry
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hself : ∀ F : Subgroup S, IsElementaryAbelian 2 F → Nat.card F = 8 →
      centralizer (F : Set S) = F)
    (hcount : ∀ F : Subgroup S, IsElementaryAbelian 2 F → Nat.card F = 8 →
      Nat.card (normalizer (F : Set S)) = 32)
    (z t : S) (hz : z ∈ center S)
    (E : Subgroup S) (hEdef : E = centralizer ({t} : Set S))
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) :
    ¬ IsConj (z : G) (t : G) := by
  intro hconj
  let U := E.map (S : Subgroup G).subtype
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  have hU : Nat.card U = 8 := by rw [card_map_of_injective (S : Subgroup G).subtype_injective, hE]
  have htE : t ∈ E := by rw [hEdef]; exact mem_centralizer_singleton_iff.mpr rfl
  have htU : (t : G) ∈ U := mem_map_of_mem _ htE
  have hUS : U ≤ (S : Subgroup G) := map_subtype_le _
  have hUC : U ≤ centralizer ({(t : G)} : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have huC : u ∈ centralizer ({t} : Set S) := hEdef ▸ hu
    exact congrArg (fun s : S => (s : G)) (mem_centralizer_singleton_iff.mp huC)
  obtain ⟨T, hUT, hTC⟩ := exists_centralizing_sylow S z hz (t : G) hconj U
    (IsElementaryAbelian.isPGroup 2 U) hUC
  let N := normalizer (U : Set G)
  let R : Subgroup G := (S : Subgroup G) ⊓ N
  let Q : Subgroup G := (T : Subgroup G) ⊓ N
  have hRN : R ≤ N := inf_le_right
  have hQN : Q ≤ N := inf_le_right
  have hUR : U ≤ R := le_inf hUS U.le_normalizer
  have hUQ : U ≤ Q := le_inf hUT U.le_normalizer
  have hcard (P : Sylow 2 G) (hUP : U ≤ P) :
      Nat.card ((P : Subgroup G) ⊓ N : Subgroup G) = 32 := by
    have hm : (N.subgroupOf (P : Subgroup G)).map (P : Subgroup G).subtype =
        (P : Subgroup G) ⊓ N := by rw [subgroupOf_map_subtype, inf_comm]
    rw [← hm, card_map_of_injective (P : Subgroup G).subtype_injective]
    exact normalizer_card_transport S P hcount U hU hUP
  have hR : Nat.card R = 32 := hcard S hUS
  have hQ : Nat.card Q = 32 := hcard T hUT
  have hCR := self_centralizer_in_psubgroup S hself U hU R S.isPGroup'.to_inf_left hUR
  have hCQ := self_centralizer_in_psubgroup S hself U hU Q T.isPGroup'.to_inf_left hUQ
  have himages := normalizer_images_eq U hU (normalizer_sylow_card_bound S hcount U hU)
    (R.subgroupOf N) (Q.subgroupOf N)
    ((Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv).trans hR)
    ((Nat.card_congr (subgroupOfEquivOfLe hQN).toEquiv).trans hQ)
    ((normalizer_kernel_card U R hRN hCR).trans hU)
    ((normalizer_kernel_card U Q hQN hCQ).trans hU)
  have hRC : R ≤ centralizer ({(t : G)} : Set G) := by
    intro r hr
    let rN : N := ⟨r, hRN hr⟩
    have hm : U.normalizerMonoidHom rN ∈ (Q.subgroupOf N).map U.normalizerMonoidHom := by
      rw [← himages]
      exact mem_map_of_mem _ hr
    obtain ⟨q, hq, heq⟩ := hm
    have hqc := mem_centralizer_singleton_iff.mp (hTC (show (q : G) ∈ T from hq.1))
    have he := congrArg (fun a : MulAut U => (a ⟨(t : G), htU⟩ : G)) heq
    change (q : G) * (t : G) * (q : G)⁻¹ = r * (t : G) * r⁻¹ at he
    have hrfix : r * (t : G) * r⁻¹ = (t : G) := by
      rw [← he, hqc, mul_assoc, mul_inv_cancel, mul_one]
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hrfix)
  have hRU : R ≤ U := by
    intro r hr
    let rS : S := ⟨r, hr.1⟩
    have hrE : rS ∈ E := by
      rw [hEdef]
      apply mem_centralizer_singleton_iff.mpr
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hRC hr))
    exact mem_map_of_mem (S : Subgroup G).subtype hrE
  have hh := card_le_of_le hRU
  rw [hR, hU] at hh
  omega
