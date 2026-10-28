module
public import Theory.GroupTheory.DihedralCentralExtensionTransfer
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.ElementaryAbelian.Injective

/-!
# Successive transfer for a fused dihedral core

A Sylow subgroup of order sixteen cannot contain an index-two fused dihedral
core together with more than two nonfused elementary involutions. For order
thirty-two, adjoining a central involution to the core gives at most five
involution classes, contradicting a nonfused elementary subgroup of order eight.
Restricting a Sylow subgroup to the two-residual and counting its intersection
with the original center therefore identifies its exact dihedral core.

Source: Aschbacher--Smith F.5.5, printed p.302. The final theorem retains the
literal ambient subgroup image for the subsequent I.4.1(2) application.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace DihedralCentralExtensionTransfer
variable {G : Type*} [Group G] [Finite G]

private theorem central_subgroup_card_le_two (U Z : Subgroup G)
    (e : U ≃* DihedralGroup 4) (hZU : Z≤U) (hZC : Z≤centralizer (U:Set G)) :
    Nat.card Z≤2 := by
  let j : Z→*center U := {
    toFun z := ⟨⟨z.val,hZU z.property⟩,mem_center_iff.mpr (fun a =>
      Subtype.ext (hZC z.property a.val a.property))⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (congrArg (fun a:center U => ((a:U):G)) he)
  have hc := DihedralGroup.center_card_of_equiv (n:=2) (by decide) e
  exact (Nat.card_le_card_of_injective j hj).trans hc.le

theorem sylow_card_ne_sixteen_of_fused_dihedral
    (S : Sylow 2 G) (hno : ∀ N:Subgroup G,N.Normal→N.index≠2)
    (U : Subgroup S) (e : U≃*DihedralGroup 4) (u:G)
    (hf : ∀ x:U, orderOf (x:S)=2 → IsConj u ((x:S):G))
    (Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZ : 2<Nat.card Z)
    (hsep : ∀x∈Z,∀y∈Z,IsConj x y→x=y) : Nat.card S≠16 := by
  intro hS
  have hU : Nat.card U=8 := by rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card]; decide +kernel
  have hi : U.index=2 := by
    have hh:=U.index_mul_card
    rw [hU,hS] at hh
    omega
  have hb := S.elementary_card_le_two_of_fused_index_two hno U hi u
    (fun v hv ho => hf ⟨v,hv⟩ ((orderOf_coe v).symm.trans ho)) Z hsep
  omega

theorem sylow_card_ne_thirtytwo_of_fused_dihedral
    (S : Sylow 2 G) (hno : ∀ N:Subgroup G,N.Normal→N.index≠2)
    (U : Subgroup S) (e : U≃*DihedralGroup 4) (u:G)
    (hf : ∀ x:U, orderOf (x:S)=2 → IsConj u ((x:S):G))
    (Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZS : Z≤S) (hZC : Z≤centralizer (S:Set G)) (hZ : 6<Nat.card Z)
    (hsep : ∀x∈Z,∀y∈Z,IsConj x y→x=y) : Nat.card S≠32 := by
  classical
  intro hS
  let U0 := U.map (S:Subgroup G).subtype
  let e0 : U0≃*DihedralGroup 4 :=
    (U.equivMapOfInjective (S:Subgroup G).subtype (S:Subgroup G).subtype_injective).symm.trans e
  have hnot : ¬Z≤U0 := by
    intro hz
    have hc := central_subgroup_card_le_two U0 Z e0 hz
      (hZC.trans (centralizer_le (map_subtype_le _)))
    omega
  obtain ⟨z,hz,hzU⟩ := SetLike.not_le_iff_exists.mp hnot
  let zS:S := ⟨z,hZS hz⟩
  have hzS : zS∉U := fun hh => hzU (mem_map_of_mem _ hh)
  have hz2 : zS^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z hz)
  have hzC : zS∈centralizer (U:Set S) := by
    intro a ha
    exact Subtype.ext (hZC hz a.val a.property)
  have hzN : zS∈normalizer (U:Set S) := centralizer_le_normalizer _ hzC
  let V := U⊔zpowers zS
  have hU : Nat.card U=8 := by rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card]; decide +kernel
  have hV : Nat.card V=16 := by
    rw [card_sup_zpowers_of_normalizing_involution U zS hz2 hzS hzN,hU]
  have hi : V.index=2 := by
    have hh:=V.index_mul_card
    rw [hV,hS] at hh
    omega
  let j : DihedralGroup 4→*G := (S:Subgroup G).subtype.comp (U.subtype.comp e.symm.toMonoidHom)
  have hj : Function.Injective j := (S:Subgroup G).subtype_injective.comp
    (U.subtype_injective.comp e.symm.injective)
  have hzj (d:DihedralGroup 4) : Commute z (j d) :=
    (hZC hz ((e.symm d:S):G) (e.symm d:S).property).symm
  have hfj (d:DihedralGroup 4) (hd:orderOf d=2) : IsConj u (j d) := by
    exact hf (e.symm d) ((orderOf_coe (e.symm d)).trans ((e.symm.orderOf_eq d).trans hd))
  have hcover (v:S) (hv:v∈V) : ∃d,(v:G)=j d ∨ (v:G)=z*j d := by
    have hm : v∈(U:Set S)*(zpowers zS:Set S) := by
      rw [←coe_mul_of_right_le_normalizer_left U (zpowers zS) (zpowers_le.mpr hzN)]
      exact hv
    obtain ⟨a,ha,b,hb,hab⟩:=hm
    change a*b=v at hab
    have hzo : orderOf zS=2 := orderOf_eq_prime hz2 (fun hh=>hzS (hh ▸ U.one_mem))
    change b∈zpowers zS at hb
    rw [mem_zpowers_iff_mem_range_orderOf,hzo] at hb
    obtain ⟨n,hn,hnb⟩:=Finset.mem_image.mp hb
    have hn2:=Finset.mem_range.mp hn
    have hn' : n=0∨n=1 := by omega
    refine ⟨e ⟨a,ha⟩,?_⟩
    have hja : j (e ⟨a,ha⟩)=(a:G) := by simp [j]
    rcases hn' with rfl|rfl
    · left
      have hb1 : b=1 := by simpa using hnb.symm
      rw [hb1,mul_one] at hab
      rw [hja,←hab]
    · right
      have hbz : b=zS := by simpa using hnb.symm
      rw [hbz] at hab
      rw [hja,←hab]
      exact hZC hz a.val a.property
  have hb:=S.elementary_card_le_six_of_dihedral_extension hno V hi j hj u z
    (elemPow_eq_one_of_isElementaryAbelian z hz) hzj hfj hcover Z hsep
  omega

theorem residual_sylow_eq_of_center_nonfusion
    (S : Sylow 2 G) (hS : Nat.card S=32)
    (Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZS : Z≤S) (hZC : Z≤centralizer (S:Set G)) (hZ : Nat.card Z=8)
    (hsep : ∀x∈Z,∀y∈Z,IsConj x y→x=y)
    (U : Subgroup G) (hUS : U≤S) (hUW : U≤pResidual 2 G)
    (e : U≃*DihedralGroup 4) (u:pResidual 2 G)
    (hf : ∀x:U, orderOf x=2 →
      IsConj u (⟨x.val,hUW x.property⟩:pResidual 2 G)) :
    ∃ P:Sylow 2 (pResidual 2 G),
      (P:Subgroup (pResidual 2 G)).map (pResidual 2 G).subtype=U := by
  let W := pResidual 2 G
  obtain ⟨P,hP⟩ := S.exists_sylow_map_eq_inf_of_normal W
  let Q := (P:Subgroup W).map W.subtype
  have hQ : Q=(S:Subgroup G)⊓W := hP
  have hUQ : U≤Q := hQ.symm ▸ le_inf hUS hUW
  have hQS : Q≤S := hQ ▸ inf_le_left
  have hUc : Nat.card U=8 := by rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card]; decide +kernel
  have hQP : Nat.card Q=Nat.card P := card_map_of_injective W.subtype_injective
  have h8P : 8∣Nat.card P := by
    rw [←hQP,←hUc]
    exact card_dvd_of_le hUQ
  have hP32 : Nat.card P∣32 := by
    rw [←hQP,←hS]
    exact card_dvd_of_le hQS
  have hc : Nat.card P=8∨Nat.card P=16∨Nat.card P=32 := by
    have hp:=Nat.le_of_dvd (by decide : 0<32) hP32
    have hh : ∀n:Fin 33,8∣n.val → n.val∣32 → n.val=8∨n.val=16∨n.val=32 := by decide +kernel
    exact hh ⟨Nat.card P,by omega⟩ h8P hP32
  let k : P→*G := W.subtype.comp (P:Subgroup W).subtype
  let UP : Subgroup P := U.comap k
  have hk : Function.Injective k := W.subtype_injective.comp (P:Subgroup W).subtype_injective
  have hUPmap : UP.map k=U := by
    rw [map_comap_eq]
    apply inf_eq_right.mpr
    simpa only [k,MonoidHom.range_comp,range_subtype] using hUQ
  let eUP : UP≃*U := (UP.equivMapOfInjective k hk).trans (MulEquiv.subgroupCongr hUPmap)
  have heUP (x:UP) : (eUP x:G)=k x.val := rfl
  have hUPfusion (x:UP) (ho:orderOf (x:P)=2) : IsConj u ((x:P):W) := by
    have hox : orderOf (eUP x)=2 := (eUP.orderOf_eq x).trans ((orderOf_coe x).symm.trans ho)
    have hh:=hf (eUP x) hox
    convert hh using 1
    exact Subtype.ext (heUP x).symm
  have hno (N:Subgroup W) (hn:N.Normal) : N.index≠2 := by
    intro hn2
    let := hn
    have he := isPPerfect_pResidual (G:=G) 2 N hn
      (IsPGroup.of_card (p:=2) (n:=1) (by simpa only [pow_one,←index_eq_card] using hn2))
    simp only [he,index_top] at hn2
    omega
  rcases hc with hc|hc|hc
  · exact ⟨P,eq_of_le_of_card_ge hUQ (by rw [hQP,hc,hUc]) |>.symm⟩
  · let ZQ := Z⊓Q
    have hZQW : ZQ≤W := inf_le_right.trans (hQ ▸ inf_le_right)
    let ZW := ZQ.subgroupOf W
    let eZW : ZW≃*ZQ := subgroupOfEquivOfLe hZQW
    let : IsElementaryAbelian 2 ZQ := IsElementaryAbelian.of_injective
      (inclusion (inf_le_left:ZQ≤Z)) (inclusion_injective _)
    let : IsElementaryAbelian 2 ZW := IsElementaryAbelian.subgroupOf hZQW
    have hZWc : Nat.card ZW=Nat.card ZQ := Nat.card_congr eZW.toEquiv
    have hlow : 2<Nat.card ZW := by
      have hh:=card_mul_eq_card_inf_mul_card_sup_of_normalizes Z Q
        ((le_centralizer_iff.mp (hZC.trans (centralizer_le hQS))).trans (centralizer_le_normalizer _))
      have hb : Nat.card (Z⊔Q:Subgroup G)≤32 := by
        rw [←hS]
        exact Nat.card_le_card_of_injective (inclusion (sup_le hZS hQS)) (inclusion_injective _)
      rw [hZ,hQP,hc,←hZWc] at hh
      have hpos:=Nat.card_pos (α:=(Z⊔Q:Subgroup G))
      nlinarith
    have hsepW : ∀x∈ZW,∀y∈ZW,IsConj x y→x=y := by
      intro x hx y hy hxy
      exact Subtype.ext (hsep x.val hx.1 y.val hy.1 (W.subtype.map_isConj hxy))
    exact (sylow_card_ne_sixteen_of_fused_dihedral P hno UP (eUP.trans e) u
      hUPfusion ZW hlow hsepW hc).elim
  · have hQS_eq : Q=(S:Subgroup G) := eq_of_le_of_card_ge hQS (by rw [hQP,hc,hS])
    have hSW : (S:Subgroup G)≤W := hQS_eq ▸ (hQ ▸ inf_le_right)
    have hZW : Z≤W := hZS.trans hSW
    let ZW := Z.subgroupOf W
    let : IsElementaryAbelian 2 ZW := IsElementaryAbelian.subgroupOf hZW
    have hZWc : Nat.card ZW=8 := (Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv).trans hZ
    have hZP : ZW≤P := by
      intro x hx
      apply (mem_map_iff_mem W.subtype_injective).mp
      change x.val∈Q
      rw [hQS_eq]
      exact hZS hx
    have hZPC : ZW≤centralizer (P:Set W) := by
      intro x hx y hy
      apply Subtype.ext
      exact hZC hx y.val (hQS (mem_map_of_mem W.subtype hy))
    have hsepW : ∀x∈ZW,∀y∈ZW,IsConj x y→x=y := by
      intro x hx y hy hxy
      exact Subtype.ext (hsep x.val hx y.val hy (W.subtype.map_isConj hxy))
    exact (sylow_card_ne_thirtytwo_of_fused_dihedral P hno UP (eUP.trans e) u
      hUPfusion ZW hZP hZPC (by omega) hsepW hc).elim

end DihedralCentralExtensionTransfer
