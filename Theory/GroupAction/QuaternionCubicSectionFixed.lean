module

public import Theory.GroupAction.QuaternionCubicFixedBound
public import Theory.GroupAction.NoncentralTwoChiefLength.Native

/-!
# The fixed preimage in the literal ternary central quotient

The quaternion-cubic bound on the actual conjugation action of S on D/W
limits the fixed subgroup to order9. Its inverse image in D has order at
most27 and contains V∩D of that order, hence is exactly V∩D. The final
criterion uses the original commutator and actual subgroup inclusions.
Source: Aschbacher, Sporadic Groups (1994),45.8(2),printed p246.
-/

public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem quaternion_cubic_section_fixed (S Q D W V:Subgroup G) [(W.subgroupOf D).Normal]
    [IsMulCommutative V] (hSD:S≤normalizer (D:Set G)) (hSW:S≤normalizer (W:Set G))
    (hQS:Q≤S) (e:Q≃*QuaternionGroup 2) (y:G) (hyS:y∈S) (hyV:y∈V)
    (c:MulAut Q) (hc:c^3=1) (hne:c≠1) (hcy:∀q:Q,(c q:G)=y*q*y⁻¹)
    (z:G) (hzQ:z∈Q) (hz:orderOf z=2)
    (hi:∀d∈D,z*d*z⁻¹*d∈W) (hD:Nat.card D=243) (hW:Nat.card W=3) (hWD:W≤D)
    (hcap:Nat.card (V⊓D:Subgroup G)=27) :
    ∀d∈D,y*d*y⁻¹*d⁻¹∈W ↔ d∈V := by
  let A:=D⧸W.subgroupOf D
  let π:=QuotientGroup.mk' (W.subgroupOf D)
  let : MulDistribMulAction S A:=quotientConjugationAction S D W hSD hSW
  let ρ:S→*MulAut A:=MulDistribMulAction.toMulAut S A
  let σ:Q→*MulAut A:=ρ.comp (inclusion hQS)
  let a:MulAut A:=ρ ⟨y,hyS⟩
  have hcompat (q:Q):a*σ q*a⁻¹=σ (c q):=by
    change ρ ⟨y,hyS⟩*ρ (inclusion hQS q)*(ρ ⟨y,hyS⟩)⁻¹=ρ (inclusion hQS (c q))
    rw [←map_inv,←map_mul,←map_mul]
    apply congrArg ρ
    apply Subtype.ext
    exact (hcy q).symm
  have hinv (x:A):σ ⟨z,hzQ⟩ x=x⁻¹:=by
    obtain ⟨d,rfl⟩:=QuotientGroup.mk'_surjective (W.subgroupOf D) x
    change π ⟨z*(d:G)*z⁻¹,_⟩=(π d)⁻¹
    apply mul_eq_one_iff_eq_inv.mp
    rw [←map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (hi d d.property)
  have hAc:Nat.card A=81:=by
    have hh:=card_eq_card_quotient_mul_card_subgroup (W.subgroupOf D)
    rw [Nat.card_congr (subgroupOfEquivOfLe hWD).toEquiv,hW,hD] at hh
    change 243=Nat.card A*3 at hh
    omega
  have hbound:=MulAut.quaternion_cubic_fixed_card_bound e c hc hne (⟨z,hzQ⟩:Q)
    (by rwa [orderOf_mk]) ((IsPGroup.of_card (n:=5) hD).to_quotient (W.subgroupOf D)) σ a hcompat hinv
  rw [hAc] at hbound
  have hf:Nat.card a.fixedSubgroup≤9:=by nlinarith
  let E:Subgroup D:=a.fixedSubgroup.comap π
  have hE:Nat.card E≤27:=by
    have hindex:E.index=a.fixedSubgroup.index:=
      a.fixedSubgroup.index_comap_of_surjective (QuotientGroup.mk'_surjective (W.subgroupOf D))
    have he:=E.card_mul_index
    have ha:=a.fixedSubgroup.card_mul_index
    rw [hindex,hD] at he
    rw [hAc] at ha
    have hn:0<a.fixedSubgroup.index:=Nat.pos_of_ne_zero (a.fixedSubgroup.index_ne_zero_of_finite)
    have heq:Nat.card E=3*Nat.card a.fixedSubgroup:=by nlinarith
    rw [heq]
    omega
  have hmem (d:D):d∈E ↔ y*(d:G)*y⁻¹*(d:G)⁻¹∈W:=by
    change π d∈a.fixedSubgroup ↔ _
    rw [MulAut.mem_fixedSubgroup]
    change π ⟨y*(d:G)*y⁻¹,_⟩=π d ↔ _
    rw [←mul_inv_eq_one,←map_inv,←map_mul]
    exact QuotientGroup.eq_one_iff _
  have hle:(V⊓D).subgroupOf D≤E:=by
    intro d hd
    apply (hmem d).mpr
    have hc:y*(d:G)=(d:G)*y:=congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨y,hyV⟩:V) ⟨d,hd.1⟩)
    simpa only [hc,mul_inv_cancel_right,mul_inv_cancel] using W.one_mem
  have hEq:(V⊓D).subgroupOf D=E:=eq_of_le_of_card_ge hle (by
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_right:V⊓D≤D)).toEquiv,hcap]
    exact hE)
  intro d hd
  rw [←hmem ⟨d,hd⟩,←hEq]
  change d∈V⊓D ↔ d∈V
  exact ⟨fun h=>h.1,fun h=>⟨h,hd⟩⟩
end Subgroup
