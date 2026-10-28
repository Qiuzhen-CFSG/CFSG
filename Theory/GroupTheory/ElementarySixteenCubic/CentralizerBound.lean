module
public import Theory.GroupAction.BinaryCubicFixedKernel
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupAction.QuotientConjugation
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Local cubic CentralizerBound

The actual normalizer centralizer acts on the moving four-group. Its kernel is the fixed four, so its order divides 24. This uses the original conjugation action and self-centralization of the elementary sixteen.
Source: Aschbacher (1994), 45.7(3).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace ElementarySixteenCubic
variable {G:Type*} [Group G] [Finite G]

theorem fixed_four_centralizer_card_dvd
    (R U:Subgroup G) [R.Normal] [IsElementaryAbelian 2 R]
    (hR:Nat.card R=16) (hU:Nat.card U=3)
    (hself:centralizer (R:Set G)≤R)
    (hRN:R⊓normalizer (U:Set G)=R⊓centralizer (U:Set G))
    (hS:Nat.card (R⊓centralizer (U:Set G):Subgroup G)=4) :
    Nat.card (normalizer (U:Set G) ⊓ centralizer
      (R⊓centralizer (U:Set G):Set G):Subgroup G) ∣24 := by
  let N:=normalizer (U:Set G)
  let S:=R⊓centralizer (U:Set G)
  let K:=N⊓centralizer (S:Set G)
  let α:G→*MulAut R:=MulAut.conjNormal
  have hker:α.ker=R:=by
    rw [MulAut.conjNormal_ker_eq_centralizer]
    apply le_antisymm hself
    intro r hr
    apply mem_centralizer_iff.mpr
    intro s hs
    exact congrArg Subtype.val (mul_comm (⟨s,hs⟩:R) ⟨r,hr⟩)
  have hp:IsPGroup 3 U:=IsPGroup.of_card (n:=1) (by simpa using hU)
  have hi:=injective_comp_subtype_of_coprime_ker α
    (show Nat.Coprime 3 (Nat.card α.ker) by rw [hker,hR]; decide) U hp
  let D:=U.map α
  have hD:Nat.card D=3:=by
    rw [show D=(α.comp U.subtype).range by rw [MonoidHom.range_comp,range_subtype],
      ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,hU]
  have hfixed:FixedPoints.subgroup D R=S.subgroupOf R:=by
    ext r
    constructor
    · intro hr
      refine ⟨r.property,mem_centralizer_iff.mpr ?_⟩
      intro u hu
      have he:=congrArg Subtype.val (hr (⟨α u,mem_map_of_mem α hu⟩:D))
      change u*(r:G)*u⁻¹=(r:G) at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hr a
      obtain ⟨u,hu,he⟩:=a.property
      change (a:MulAut R) r = r
      rw [← he]
      apply Subtype.ext
      change u*(r:G)*u⁻¹=(r:G)
      have hh:u*(r:G)=(r:G)*u:=mem_centralizer_iff.mp hr.2 u hu
      rw [hh,mul_inv_cancel_right]
  have hF:Nat.card (FixedPoints.subgroup D R)=4:=by
    rw [hfixed,Nat.card_congr (subgroupOfEquivOfLe (show S≤R from inf_le_left)).toEquiv]
    exact hS
  let L:=normalizer (D:Set (MulAut R)) ⊓
    fixingSubgroup (MulAut R) (FixedPoints.subgroup D R:Set R)
  have hL:Nat.card L∣6:=Theory.GroupAction.cubic_fixed_kernel_card_dvd_six hR D hD hF
  have hKL:K.map α≤L:=by
    rintro a ⟨k,hk,rfl⟩
    refine ⟨U.le_normalizer_map α (mem_map_of_mem α hk.1), ?_⟩
    apply (mem_fixingSubgroup_iff (MulAut R)).mpr
    intro r hr
    have hrs:(r:G)∈S:=by rw [hfixed] at hr; exact hr
    apply Subtype.ext
    change k*(r:G)*k⁻¹=(r:G)
    rw [← mem_centralizer_iff.mp hk.2 r hrs,mul_inv_cancel_right]
  have hSK:S≤K:=by
    intro s hs
    refine ⟨centralizer_le_normalizer _ hs.2,mem_centralizer_iff.mpr ?_⟩
    intro r hr
    exact congrArg Subtype.val (mul_comm (⟨r,hr.1⟩:R) ⟨s,hs.1⟩)
  have hKR:K⊓R=S:=by
    apply le_antisymm ?_ (le_inf hSK inf_le_left)
    rintro k ⟨hk,hkR⟩
    exact hRN.le ⟨hkR,hk.1⟩
  let β:=α.comp K.subtype
  have hβker:β.ker=S.subgroupOf K:=by
    ext x
    change α (x:G)=1 ↔ (x:G)∈S
    change (x:G)∈α.ker ↔ _
    rw [hker]
    exact ⟨fun hx=>hKR.le ⟨x.property,hx⟩,fun hx=>hx.1⟩
  have hβcard:Nat.card β.ker=4:=by
    rw [hβker,Nat.card_congr (subgroupOfEquivOfLe hSK).toEquiv];exact hS
  have hβrange:β.range=K.map α:=by rw [MonoidHom.range_comp,range_subtype]
  have hd:Nat.card β.range∣6:=by
    rw [hβrange];exact (card_dvd_of_le hKL).trans hL
  have hcard:=β.ker.card_mul_index
  rw [hβcard,index_ker] at hcard
  change Nat.card K∣24
  rw [←hcard]
  exact Nat.mul_dvd_mul_left 4 hd
end ElementarySixteenCubic
