module

public import Theory.GroupAction.QuaternionSixteenTernaryDegree
public import Theory.GroupAction.NoncentralTwoChiefLength.Native
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.Frattini.PGroup
public import Theory.ElementaryAbelian.Injective

/-!
# Original quaternion conjugation on a cubic section

A marked Q16 normalizing D and W acts on the literal quotient D/W.
Its unique involution is identified with the given z, so the source
inversion relation descends unchanged. The elementary quaternion orbit
bound forces a nontrivial ternary section of order at most81 to have
order81. Applied again to its Frattini quotient, it forces that section
to be elementary. Consequently a cubic central kernel gives |D|=243.

The final helper chooses a quaternion Sylow containing the actual z;
it does not replace the involution by an unmarked conjugate.
Source: Aschbacher, Sporadic Groups (1994),45.8,printed p246.
-/

public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G]
theorem quaternion_sixteen_section_action (S D W:Subgroup G) [(W.subgroupOf D).Normal]
    (e:S≃*QuaternionGroup 4) (z:G) (hzS:z∈S) (hz:orderOf z=2)
    (hSD:S≤normalizer (D:Set G)) (hSW:S≤normalizer (W:Set G))
    (hi:∀d∈D,z*d*z⁻¹*d∈W) :
    ∃ρ:QuaternionGroup 4→*MulAut (D⧸W.subgroupOf D),
      ∀x,ρ (QuaternionGroup.a 4) x=x⁻¹ := by
  let : MulDistribMulAction S (D⧸W.subgroupOf D):=quotientConjugationAction S D W hSD hSW
  let ρ:QuaternionGroup 4→*MulAut (D⧸W.subgroupOf D):=
    (MulDistribMulAction.toMulAut S (D⧸W.subgroupOf D)).comp e.symm.toMonoidHom
  have he:e ⟨z,hzS⟩=QuaternionGroup.a 4:=by
    have ho:orderOf (e ⟨z,hzS⟩)=2:=by rw [e.orderOf_eq,orderOf_mk,hz]
    have hn:e ⟨z,hzS⟩≠1:=by intro hh;simp [hh] at ho
    have hs:(e ⟨z,hzS⟩)^2=1:=by simpa only [ho] using pow_orderOf_eq_one (e ⟨z,hzS⟩)
    exact (by decide:∀y:QuaternionGroup 4,y≠1→y^2=1→y=QuaternionGroup.a 4) _ hn hs
  refine ⟨ρ,?_⟩
  intro x
  obtain ⟨d,rfl⟩:=QuotientGroup.mk'_surjective (W.subgroupOf D) x
  rw [←he]
  change QuotientGroup.mk' (W.subgroupOf D)
    ⟨(e.symm (e ⟨z,hzS⟩):G)*(d:G)*(e.symm (e ⟨z,hzS⟩):G)⁻¹,_⟩=
      (QuotientGroup.mk' (W.subgroupOf D) d)⁻¹
  simp only [e.symm_apply_apply]
  apply mul_eq_one_iff_eq_inv.mp
  rw [←map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact hi d d.property
end Subgroup
namespace Subgroup
variable {A:Type*} [Group A] [Finite A] [Nontrivial A]
theorem quaternion_inverted_section_elementary (hA:IsPGroup 3 A) (hcard:Nat.card A≤81)
    (ρ:QuaternionGroup 4→*MulAut A) (hz:∀a,ρ (QuaternionGroup.a 4) a=a⁻¹) :
    Nat.card A=81 ∧ IsElementaryAbelian 3 A := by
  have hAc:Nat.card A=81:=Nat.le_antisymm hcard
    (Theory.GroupAction.QuaternionSixteenTernaryDegree.card_ge_eighty_one_of_inversion hA ρ hz)
  let F:=frattini A
  have hF:F≠⊤:=by
    intro he
    exact bot_ne_top (frattini_nongenerating (K:=(⊥:Subgroup A)) (by simpa only [bot_sup_eq] using he))
  let : Nontrivial (A⧸F):=QuotientGroup.nontrivial_iff.mpr hF
  let : Fact (IsPGroup 3 A):=⟨hA⟩
  let : IsElementaryAbelian 3 (A⧸F):=isElementaryAbelian_quotient_frattini
  let σ:QuaternionGroup 4→*MulAut (A⧸F):=(quotientAut F).comp ρ
  have hi:∀x,σ (QuaternionGroup.a 4) x=x⁻¹:=by
    intro x
    obtain ⟨a,rfl⟩:=QuotientGroup.mk'_surjective F x
    change quotientAut F (ρ (QuaternionGroup.a 4)) (QuotientGroup.mk' F a)=_
    rw [quotientAut_apply_mk,hz,map_inv]
  have hbc:81≤Nat.card (A⧸F):=
    Theory.GroupAction.QuaternionSixteenTernaryDegree.card_ge_eighty_one_of_elementary_inversion σ hi
  have hb:Nat.card (A⧸F)≤81:=(Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective F)).trans hcard
  have hFe:F=⊥:=by
    have hh:=(card_eq_card_quotient_mul_card_subgroup F).symm
    rw [Nat.le_antisymm hb hbc,hAc] at hh
    exact Subgroup.card_eq_one.mp (by omega)
  have hinj:Function.Injective (QuotientGroup.mk' F):=by
    rw [←MonoidHom.ker_eq_bot_iff,QuotientGroup.ker_mk',hFe]
  exact ⟨hAc,IsElementaryAbelian.of_injective (QuotientGroup.mk' F) hinj⟩
end Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem quaternion_inverted_section_order (S D W:Subgroup G) [(W.subgroupOf D).Normal]
    (e:S≃*QuaternionGroup 4) (z:G) (hzS:z∈S) (hz:orderOf z=2)
    (hSD:S≤normalizer (D:Set G)) (hSW:S≤normalizer (W:Set G))
    (hWD:W≤D) (hW:Nat.card W=3) (hD:Nat.card D∣243) (hlo:27≤Nat.card D)
    (hi:∀d∈D,z*d*z⁻¹*d∈W) :
    Nat.card D=243 ∧ Nat.card (D⧸W.subgroupOf D)=81 ∧
      IsElementaryAbelian 3 (D⧸W.subgroupOf D) := by
  let A:=D⧸W.subgroupOf D
  have hKc:Nat.card (W.subgroupOf D)=3:=by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWD).toEquiv,hW]
  have hh:=(card_eq_card_quotient_mul_card_subgroup (W.subgroupOf D)).symm
  rw [hKc] at hh
  have hlarge:9≤Nat.card A:=by change Nat.card A*3=Nat.card D at hh;omega
  let : Nontrivial A:=Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hup:Nat.card A≤81:=by
    have hd:=Nat.le_of_dvd (by decide:0<243) hD
    change Nat.card A*3=Nat.card D at hh
    omega
  have hp:IsPGroup 3 D:=IsPGroup.of_card_dvd_pow (n:=5) hD
  obtain ⟨ρ,hρ⟩:=quaternion_sixteen_section_action S D W e z hzS hz hSD hSW hi
  obtain ⟨hAc,hAe⟩:=quaternion_inverted_section_elementary (hp.to_quotient (W.subgroupOf D)) hup ρ hρ
  refine ⟨?_,hAc,hAe⟩
  change Nat.card A*3=Nat.card D at hh
  rw [hAc] at hh
  omega

theorem exists_marked_quaternion_subgroup (M:Subgroup G) (z:G) (hzM:z∈M)
    (hz:orderOf z=2) (P:Sylow 2 M) (hP:Nonempty (P≃*QuaternionGroup 4)) :
    ∃S:Subgroup G,Nonempty (S≃*QuaternionGroup 4) ∧ S≤M ∧ z∈S := by
  let zz:M:=⟨z,hzM⟩
  have hz2:orderOf zz=2:=by rwa [orderOf_mk]
  have hp:IsPGroup 2 (zpowers zz):=IsPGroup.of_card (n:=1) (by simp [Nat.card_zpowers,hz2])
  obtain ⟨Q,hQ⟩:=hp.exists_le_sylow
  let S:Subgroup G:=(Q:Subgroup M).map M.subtype
  refine ⟨S,⟨((Q:Subgroup M).equivMapOfInjective M.subtype M.subtype_injective).symm.trans
    ((Q.equiv P).trans hP.some)⟩,map_subtype_le _,?_⟩
  exact ⟨zz,hQ (mem_zpowers zz),rfl⟩
end Subgroup
