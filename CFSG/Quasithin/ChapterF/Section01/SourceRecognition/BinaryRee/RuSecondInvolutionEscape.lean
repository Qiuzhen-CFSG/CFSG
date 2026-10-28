module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondExtensionInvariants
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCoreInvolutions
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondBadCoset.Square

/-!
# Source involutions exclude the twisted middle lift

The original A has 79 involutions and the unchanged T_F has 143, hence an
involution lies outside A. The actual index-two calculation writes it in any
outside A-coset. Consequently a lift with the specified twisted action and
root-seven square cannot occur in this same original middle.

Source: the binary Ree branch of Aschbacher–Smith F.1.12 applied in J.4.5.
The source normalizer owner constructs the possible lift alternatives; this
module excludes the twisted alternative using literal original subgroup data.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Subgroup Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

/-- The original second core has the native involution count. -/
theorem SourceChoice.A_involution_card (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nat.card {a:p.A B5 // orderOf a=2}=79 := by
  obtain ⟨_,e,_⟩:=s.exists_T_F_A_marking B5 hi
  let f : {a:p.A B5 // orderOf a=2}≃{a:ReeTwo.SylowModel.CubicAction.A // orderOf a=2} :=
    Equiv.subtypeEquiv e.toEquiv (fun a=>by
      change (orderOf a=2)↔(orderOf (e a)=2)
      exact Iff.of_eq ((congrArg (·=2) (orderOf_injective e.toMonoidHom e.injective a)).symm))
  rw [Nat.card_congr f]
  exact ReeTwo.SylowModel.CollectedBitVectors.core_involution_card

/-- A genuine source-middle involution lies outside the original second core. -/
theorem SourceChoice.exists_T_F_involution_not_A (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃t:p.T_F B5,orderOf t=2 ∧ (t:G)∉p.A B5 := by
  by_contra h
  push Not at h
  let f : {t:p.T_F B5 // orderOf t=2}→{a:p.A B5 // orderOf a=2} := fun t=>
    ⟨⟨(t.val:G),h t.val t.property⟩,by
      simpa only [Subgroup.orderOf_mk,Subgroup.orderOf_coe] using t.property⟩
  have hf:Function.Injective f := by
    intro t u hu
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x:{a:p.A B5 // orderOf a=2}=>(x.val:G)) hu
  have hc:=Nat.card_le_card_of_injective f hf
  rw [s.T_F_involution_card B5 hi,s.A_involution_card B5 hi] at hc
  omega

end CFSG.Quasithin.ChapterJ.RuSubgroup

namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Subgroup Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

/-- The twisted action and lift square cannot occur on the original middle. -/
theorem SourceChoice.no_twisted_middle_lift (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (e:p.A B5≃*ReeTwo.SylowModel.CubicAction.A)
    (v:p.T_F B5) (hv:(v:G)∉p.A B5)
    (hact:∀a:p.A B5,(e.symm (ReeTwo.SylowModel.CubicAction.badActor (e a)):G)=
      (v:G)*(a:G)*(v:G)⁻¹)
    (hsq:(v:G)^2=(e.symm (ReeTwo.SylowModel.CubicAction.generator 7):G)) : False := by
  obtain ⟨t,ht,htA⟩:=s.exists_T_F_involution_not_A B5 hi
  let D:Subgroup (p.T_F B5):=(p.A B5).subgroupOf (p.T_F B5)
  have hD:Nat.card D=2048 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show p.A B5≤p.T_F B5 from le_sup_left)).toEquiv,
      s.card_A p B5 hi]
  have hidx:D.index=2 := by
    have h:=D.card_mul_index
    rw [hD,s.card_T_F p B5 hi] at h
    omega
  have hu:t*v⁻¹∈D := (mul_mem_iff_of_index_two hidx).mpr (by
    change ((t:G)∈p.A B5)↔((v:G)⁻¹∈p.A B5)
    simp only [htA,inv_mem_iff,hv])
  let a:p.A B5:=⟨((t*v⁻¹:p.T_F B5):G),hu⟩
  have htv:(a:G)*(v:G)=(t:G) := by
    change ((t:G)*(v:G)⁻¹)*(v:G)=(t:G)
    group
  have ht2:(t:G)^2=1 := by
    have h:=congrArg (fun y:p.T_F B5=>(y:G)) (ht ▸ pow_orderOf_eq_one t)
    exact h
  apply ReeTwo.SylowModel.CollectedBitVectors.bad_coset_square_ne_one (e a)
  apply e.symm.injective
  apply Subtype.ext
  simp only [map_mul,map_one,e.symm_apply_apply,Subgroup.coe_mul,Subgroup.coe_one]
  rw [hact,←hsq]
  calc
    (a:G)*((v:G)*(a:G)*(v:G)⁻¹)*(v:G)^2=((a:G)*(v:G))^2 := by
      simp only [pow_two]
      group
    _ = 1 := by rw [htv,ht2]

end CFSG.Quasithin.ChapterJ.RuSubgroup
