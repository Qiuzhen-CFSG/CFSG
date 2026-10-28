module
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Index
/-!
# Elementary subgroups of an index-two central supplement

Suppose every involution of I lies in J and s is a central involution
outside I. An elementary subgroup of an overgroup of I⟨s⟩ of index at
most two has order at most four times |J|. Intersect with I⟨s⟩ and
project to I to bound that intersection by J⟨s⟩.

This general count is used in the single-block fusion argument on
Aschbacher–Smith, printed p.539.
-/
public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem elementary_card_le_of_central_involution_index_two
    (P I J E : Subgroup G) [IsElementaryAbelian 2 E]
    (hEP : E≤P) (hJI : J≤I) (s:G) (hs2 : s^2=1) (hsI : s∉I)
    (hsC : s∈centralizer (I:Set G))
    (hInv : ∀ r : G, r ∈ I → r ^ 2 = 1 → r ∈ J)
    (hindex : (I⊔zpowers s).relIndex P≤2) : Nat.card E≤4*Nat.card J := by
  let K := I⊔zpowers s
  have hzC : zpowers s≤centralizer (I:Set G) := zpowers_le.mpr hsC
  have hB : K⊓E≤J⊔zpowers s := by
    intro b hb
    have hbprod : b∈(I:Set G)*(zpowers s:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left I (zpowers s)
        (hzC.trans (Subgroup.centralizer_le_normalizer _))]
      exact hb.1
    obtain ⟨r,hr,y,hy,he⟩ := hbprod
    have hyr : Commute r y := mem_centralizer_iff.mp (hzC hy) r hr
    have hy2 : y^2=1 := by
      obtain ⟨j,rfl⟩ := hy
      rw [←zpow_natCast,←zpow_mul,Int.mul_comm,zpow_mul,zpow_natCast,hs2,one_zpow]
    have hb2 : b^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) b hb.2
    have hr2 : r^2=1 := by
      rw [←he,hyr.mul_pow,hy2,mul_one] at hb2
      exact hb2
    exact he ▸ mul_mem_sup (hInv r hr hr2) hy
  have hsJ : s∉J := fun h=>hsI (hJI h)
  have hsNJ : s∈normalizer (J:Set G) :=
    (Subgroup.centralizer_le_normalizer (J : Set G)) (centralizer_le hJI hsC)
  have hcard : Nat.card (J⊔zpowers s : Subgroup G)=2*Nat.card J :=
    card_sup_zpowers_of_normalizing_involution J s hs2 hsJ hsNJ
  have hcB : Nat.card (K⊓E : Subgroup G)≤2*Nat.card J := by
    rw [←hcard]
    exact Nat.card_le_card_of_injective (inclusion hB) (inclusion_injective hB)
  have hcE : Nat.card (K⊓E : Subgroup G)*K.relIndex E=Nat.card E := by
    have h := relIndex_mul_relIndex (⊥:Subgroup G) (K⊓E) E bot_le inf_le_right
    simpa only [relIndex_bot_left,inf_relIndex_right] using h
  have hind : K.relIndex E≤2 :=
    (relIndex_le_of_le_right hEP (by change (K.subgroupOf P).index≠0; exact index_ne_zero_of_finite)).trans hindex
  rw [←hcE]
  nlinarith
end Subgroup
