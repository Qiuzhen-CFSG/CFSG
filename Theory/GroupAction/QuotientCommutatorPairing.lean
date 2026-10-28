module
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The quotient commutator pairing for a centralizing source group

Suppose V≤B, B centralizes V, [B,U]≤V and [V,U]≤Z. For the literal normal
quotient V/(Z.subgroupOf V), assumed commutative, commutators define a
homomorphism B →* (U →* V/Z). B itself need not be commutative. Evaluation
is the actual ambient commutator, and the range of its b-th member is exactly
the image of [<b>,U] in V/Z. No ambient normality of B or U is required.
The original abelian-B definition and its apply/range theorems remain exact
specializations: V≤B and B commutative imply the needed centralization.

The two commutator product identities give the homomorphism laws. U
centralizes V modulo Z. For the first variable, B centralizes each commutator
in V; since V≤B, the two commutators also commute with one another. Powers
in that variable then identify the cyclic-commutator image with the range in
the second variable. The original private quotient-conjugation argument is
shared by both public interfaces.

This source-neutral algebra supplies the small-image family in Stellmacher
(10.1)(16), printed p.64, and the centralizing-source family in (20), printed
p.65, Journal of Algebra 190 (1997).
-/

namespace Subgroup
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type*} [Group G] (B U V Z : Subgroup G)
    [IsMulCommutative B] [hN : (Z.subgroupOf V).Normal]
    [IsMulCommutative (V ⧸ Z.subgroupOf V)]
    (hVB : V ≤ B) (hBU : ⁅B,U⁆ ≤ V) (hVU : ⁅V,U⁆ ≤ Z)

omit [IsMulCommutative B] [IsMulCommutative (V ⧸ Z.subgroupOf V)] in
include hVB hBU hVU in
private theorem quotient_commutator_conjugate (u : U) (v : V) :
    ∃ hv : (u:G) * (v:G) * (u:G)⁻¹ ∈ V,
      QuotientGroup.mk' (Z.subgroupOf V) ⟨(u:G)*(v:G)*(u:G)⁻¹,hv⟩ =
        QuotientGroup.mk' (Z.subgroupOf V) v := by
  have hc : ⁅(u:G),(v:G)⁆ ∈ Z := by
    rw [Subgroup.commutator_comm] at hVU
    exact hVU (Subgroup.commutator_mem_commutator u.property v.property)
  have hcV : ⁅(u:G),(v:G)⁆ ∈ V := by
    rw [Subgroup.commutator_comm] at hBU
    exact hBU (Subgroup.commutator_mem_commutator u.property (hVB v.property))
  have hv : (u:G)*(v:G)*(u:G)⁻¹ ∈ V := by
    have := V.mul_mem hcV v.property
    simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using this
  refine ⟨hv,?_⟩
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (u:G)*(v:G)*(u:G)⁻¹ / (v:G) ∈ Z
  simpa only [commutatorElement_def,div_eq_mul_inv] using hc

omit [IsMulCommutative B] in
public noncomputable def centralQuotientCommutatorPairing
    (hVB : V ≤ B) (hBV : B ≤ centralizer (V : Set G)) (hBU : ⁅B,U⁆ ≤ V) (hVU : ⁅V,U⁆ ≤ Z) : B →* (U →* (V ⧸ Z.subgroupOf V)) where
  toFun b := {
    toFun := fun u => QuotientGroup.mk' (Z.subgroupOf V)
      ⟨⁅(b:G),(u:G)⁆, hBU (Subgroup.commutator_mem_commutator b.property u.property)⟩
    map_one' := by
      apply (QuotientGroup.eq_one_iff _).mpr
      change ⁅(b:G),1⁆ ∈ Z
      simp
    map_mul' := by
      intro u v
      obtain ⟨hc,hq⟩ := quotient_commutator_conjugate B U V Z hVB hBU hVU u
        ⟨⁅(b:G),(v:G)⁆,hBU (Subgroup.commutator_mem_commutator b.property v.property)⟩
      rw [← hq, ← map_mul]
      congr 1
      apply Subtype.ext
      simpa only [Subgroup.coe_mul,mul_assoc] using
        commutatorElement_mul_right_eq_mul_conj (b:G) (u:G) (v:G) }
  map_one' := by
    ext u
    apply (QuotientGroup.eq_one_iff _).mpr
    change ⁅(1:G),(u:G)⁆ ∈ Z
    simp
  map_mul' := by
    intro b c
    ext u
    change QuotientGroup.mk' (Z.subgroupOf V) _ =
      QuotientGroup.mk' (Z.subgroupOf V) ⟨⁅(b:G),(u:G)⁆,_⟩ *
      QuotientGroup.mk' (Z.subgroupOf V) ⟨⁅(c:G),(u:G)⁆,_⟩
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    change ⁅(b:G)*(c:G),(u:G)⁆ = ⁅(b:G),(u:G)⁆ * ⁅(c:G),(u:G)⁆
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hc := hBU (Subgroup.commutator_mem_commutator c.property u.property)
    have hb := hBU (Subgroup.commutator_mem_commutator b.property u.property)
    have hbc : (b:G)*⁅(c:G),(u:G)⁆ = ⁅(c:G),(u:G)⁆*(b:G) :=
      (mem_centralizer_iff.mp (hBV b.property) _ hc).symm
    have hcb : ⁅(c:G),(u:G)⁆*⁅(b:G),(u:G)⁆ = ⁅(b:G),(u:G)⁆*⁅(c:G),(u:G)⁆ :=
      (mem_centralizer_iff.mp (hBV (hVB hc)) _ hb).symm
    rw [hbc,mul_inv_cancel_right,hcb]

omit [IsMulCommutative B] in
public theorem centralQuotientCommutatorPairing_apply
    (hVB : V ≤ B) (hBV : B ≤ centralizer (V : Set G))
    (hBU : ⁅B,U⁆ ≤ V) (hVU : ⁅V,U⁆ ≤ Z) (b:B) (u:U) :
    centralQuotientCommutatorPairing B U V Z hVB hBV hBU hVU b u =
      QuotientGroup.mk' (Z.subgroupOf V)
        ⟨⁅(b:G),(u:G)⁆,hBU (Subgroup.commutator_mem_commutator b.property u.property)⟩ := by rfl

omit [IsMulCommutative B] in
public theorem centralQuotientCommutatorPairing_range
    (hVB : V ≤ B) (hBV : B ≤ centralizer (V : Set G))
    (hBU : ⁅B,U⁆ ≤ V) (hVU : ⁅V,U⁆ ≤ Z) (b:B) :
    (centralQuotientCommutatorPairing B U V Z hVB hBV hBU hVU b).range =
      (⁅Subgroup.zpowers (b:G),U⁆.subgroupOf V).map
        (QuotientGroup.mk' (Z.subgroupOf V)) := by
  let f := centralQuotientCommutatorPairing B U V Z hVB hBV hBU hVU
  let π := QuotientGroup.mk' (Z.subgroupOf V)
  apply le_antisymm
  · rintro w ⟨u,rfl⟩
    refine ⟨⟨⁅(b:G),(u:G)⁆,hBU
      (Subgroup.commutator_mem_commutator b.property u.property)⟩, ?_, rfl⟩
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers _) u.property
  · let D := ((f b).range.comap π).map V.subtype
    have hle : ⁅Subgroup.zpowers (b:G),U⁆ ≤ D := by
      apply Subgroup.commutator_le.mpr
      intro c hc u hu
      obtain ⟨n,rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      have hv : ⁅(b:G)^n,u⁆ ∈ V := hBU
        (Subgroup.commutator_mem_commutator (B.zpow_mem b.property n) hu)
      refine ⟨⟨_,hv⟩,?_,rfl⟩
      change π ⟨_,hv⟩ ∈ (f b).range
      refine ⟨(⟨u,hu⟩:U)^n,?_⟩
      change f b ((⟨u,hu⟩:U)^n) = f (b^n) ⟨u,hu⟩
      rw [map_zpow,map_zpow]
      rfl
    rintro w ⟨v,hv,rfl⟩
    obtain ⟨x,hx,hxv⟩ := hle hv
    have hxv' : x = v := Subtype.ext hxv
    exact hxv' ▸ hx

public noncomputable def quotientCommutatorPairing
    (hVB : V ≤ B) (hBU : ⁅B,U⁆ ≤ V) (hVU : ⁅V,U⁆ ≤ Z) : B →* (U →* (V ⧸ Z.subgroupOf V)) :=
  centralQuotientCommutatorPairing B U V Z hVB
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hVB)) hBU hVU

public theorem quotientCommutatorPairing_apply (b:B) (u:U) :
    quotientCommutatorPairing B U V Z hVB hBU hVU b u =
      QuotientGroup.mk' (Z.subgroupOf V)
        ⟨⁅(b:G),(u:G)⁆,hBU (Subgroup.commutator_mem_commutator b.property u.property)⟩ := by rfl

public theorem quotientCommutatorPairing_range (b:B) :
    (quotientCommutatorPairing B U V Z hVB hBU hVU b).range =
      (⁅Subgroup.zpowers (b:G),U⁆.subgroupOf V).map
        (QuotientGroup.mk' (Z.subgroupOf V)) := by
  exact centralQuotientCommutatorPairing_range B U V Z hVB
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hVB)) hBU hVU b

end Subgroup
