module
public import Theory.SpecificGroups.AlternatingSix.GoldenClassGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry.Choice.Alternating
public import Theory.GroupTheory.OddInvolutionEndpointModels
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Cubic normalizers in the actual alternating group on six letters

The checked two cycle types give normalizer order18 and centralizer order9.
Their inverting involution inverts the entire centralizer; quotienting by the
original cubic line therefore gives the literal symmetric-three quotient.
No new finite enumeration or ambient classification assumption is used.
Source: Aschbacher, Sporadic Groups (1994),45.7, printed p.245.
-/

public noncomputable section
open Subgroup
namespace AlternatingSix.CubicNormalizer
abbrev A6 := alternatingGroup (Fin 6)
open Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups.ReflectionChoice

private theorem generator (U:Subgroup A6) (hU:Nat.card U=3) :
    ∃x:A6,orderOf x=3 ∧ U=zpowers x := by
  obtain ⟨x,hx⟩:=exists_prime_orderOf_dvd_card' (G:=U) 3 (hU ▸ dvd_rfl)
  have ho:orderOf (x:A6)=3 := (orderOf_injective U.subtype U.subtype_injective x).trans hx
  have he:zpowers (x:A6)=U := eq_of_le_of_card_ge (zpowers_le.mpr x.property) (by rw [Nat.card_zpowers,ho,hU])
  exact ⟨x,ho,he.symm⟩

theorem normalizer_data (U:Subgroup A6) (hU:Nat.card U=3) :
    Nat.card (normalizer (U:Set A6))=18 ∧ Nat.card (centralizer (U:Set A6))=9 ∧
      ∃t∈normalizer (U:Set A6),orderOf t=2 ∧
        ∀c∈centralizer (U:Set A6),t*c*t⁻¹=c⁻¹ := by
  obtain ⟨x,hx,rfl⟩:=generator U hU
  obtain ⟨hN,t,ht,hti,hcover⟩:=a6_three_normalizer x hx
  have hC:Nat.card (centralizer (zpowers x:Set A6))=9 := by
    have he : centralizer (zpowers x:Set A6)=centralizer ({x}:Set A6) := by
      ext y
      constructor
      · intro hy
        exact mem_centralizer_singleton_iff.mpr (hy x (mem_zpowers x)).symm
      · intro hy c hc
        obtain ⟨n,rfl⟩:=mem_zpowers_iff.mp hc
        exact ((show Commute y x from mem_centralizer_singleton_iff.mp hy).zpow_right n).symm.eq
    rw [he]
    exact AlternatingSix.GoldenClassGeometry.centralizer_three x hx
  refine ⟨hN,hC,t,(normalizes_three_iff x t hx).mpr (Or.inr hti),ht,?_⟩
  intro c hc
  have hcN:=centralizer_le_normalizer (zpowers x:Set A6) hc
  have hodd:Odd (orderOf c) := (show Odd 9 by decide).of_dvd_nat (hC ▸ (centralizer (zpowers x:Set A6)).orderOf_dvd_natCard hc)
  rcases hcover c hcN with rfl | ⟨hc2,_⟩ | ⟨htc,_⟩
  · simp
  · rw [hc2] at hodd
    norm_num at hodd
  · have ht2:t^2=1 := ht ▸ pow_orderOf_eq_one t
    have htc2:(t*c)^2=1 := htc ▸ pow_orderOf_eq_one (t*c)
    have hti':t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
    rw [hti']
    exact eq_inv_iff_mul_eq_one.mpr (by simpa only [pow_two,mul_assoc] using htc2)


private theorem normalizer_quotient_model (U:Subgroup A6) (hU:Nat.card U=3) :
    Nonempty ((normalizer (U:Set A6) ⧸ U.subgroupOf (normalizer (U:Set A6)))≃*Equiv.Perm (Fin 3)) := by
  let N:=normalizer (U:Set A6)
  let Un:=U.subgroupOf N
  let C:=centralizer (U:Set A6)
  let Cn:=C.subgroupOf N
  let q:=QuotientGroup.mk' Un
  let D:=Cn.map q
  obtain ⟨hN,hC,t,htN,ht2,hinv⟩:=normalizer_data U hU
  have hUC:U≤C := by
    let : IsMulCommutative U := (isCyclic_of_prime_card hU).isMulCommutative
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hUnCn:Un≤Cn := subgroupOf_mono N hUC
  have hUn:Nat.card Un=3 := (Nat.card_congr (subgroupOfEquivOfLe U.le_normalizer).toEquiv).trans hU
  have hCn:Nat.card Cn=9 := (Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (U:Set A6))).toEquiv).trans hC
  have hD:Nat.card D=3 := by
    have hh:=(q.ker.subgroupOf Cn).index_mul_card
    change q.ker.relIndex Cn * Nat.card (q.ker.subgroupOf Cn)=Nat.card Cn at hh
    have hk:q.ker=Un := QuotientGroup.ker_mk' Un
    rw [relIndex_ker,hk,Nat.card_congr (subgroupOfEquivOfLe hUnCn).toEquiv,hUn,hCn] at hh
    change Nat.card D*3=9 at hh
    omega
  have hquot:Nat.card (N⧸Un)=6 := by
    have hh:=card_eq_card_quotient_mul_card_subgroup Un
    rw [hUn,hN] at hh
    omega
  let tN:N:=⟨t,htN⟩
  let s:=q tN
  have hs2:s^2=1 := by
    rw [←map_pow]
    exact congrArg q (show tN^2=1 from Subtype.ext (ht2 ▸ pow_orderOf_eq_one t))
  have htC:t∉C := by
    intro hh
    have hd:=C.orderOf_dvd_natCard hh
    rw [ht2,hC] at hd
    norm_num at hd
  have hsD:s∉D := by
    intro hs
    have hm:tN∈(Cn.map q).comap q := hs
    rw [comap_map_eq,show q.ker=Un from QuotientGroup.ker_mk' Un,sup_eq_left.mpr hUnCn] at hm
    exact htC hm
  have hsinv:∀x∈D,s*x*s⁻¹=x⁻¹ := by
    rintro x ⟨c,hc,rfl⟩
    change q tN*q c*(q tN)⁻¹=(q c)⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    apply congrArg q
    exact Subtype.ext (hinv c hc)
  obtain ⟨e⟩:=nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted D s
    (isCyclic_of_prime_card hD) hs2 hsD hsinv
  have htop:D⊔zpowers s=⊤ := by
    apply eq_of_le_of_card_ge le_top
    rw [card_top,hquot,Nat.card_congr e.toEquiv,DihedralGroup.nat_card,hD]
  obtain ⟨d⟩:=Theory.GroupTheory.nonempty_dihedralThreeEquivPerm
  have hmodel:Nonempty ((D⊔zpowers s:Subgroup (N⧸Un))≃*DihedralGroup 3) := by
    rw [←hD]
    exact ⟨e⟩
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop).symm).trans (hmodel.some.trans d)⟩

/-- The original cubic normalizer in A6 has the literal S3 quotient by its cubic subgroup. -/
theorem quotient_equiv (U:Subgroup A6) (hU:Nat.card U=3) :
    Nonempty ((normalizer (U:Set A6) ⧸ U.subgroupOf (normalizer (U:Set A6)))≃*Equiv.Perm (Fin 3)) :=
  normalizer_quotient_model U hU

theorem exists_symmetric_three_surjection (U:Subgroup A6) (hU:Nat.card U=3) :
    ∃f:normalizer (U:Set A6)→*Equiv.Perm (Fin 3),Function.Surjective f ∧
      f.ker=U.subgroupOf (normalizer (U:Set A6)) := by
  obtain ⟨e⟩:=quotient_equiv U hU
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _),?_⟩
  ext x
  change e (QuotientGroup.mk' _ x)=1 ↔ _
  rw [e.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

end AlternatingSix.CubicNormalizer
