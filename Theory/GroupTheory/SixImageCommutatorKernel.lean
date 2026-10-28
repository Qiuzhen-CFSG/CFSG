module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The two reflection images in a group of order six

A nontrivial element of one order-two subgroup cannot normalize the other
when they generate a group of order six: otherwise their join is a two-group.
Consequently, in a group with such an image, an element of the second factor
commuting with the first modulo the kernel must lie in that kernel.
This supplies the core-placement step in Aschbacher--Smith13.7.10(4), p.942.
-/

public section

open Subgroup
namespace Subgroup
variable {K:Type*} [Group K] [Finite K]
theorem second_inf_normalizer_eq_bot_of_six (A B:Subgroup K)
    (hA:Nat.card A=2) (hB:Nat.card B=2) (hAB:Nat.card (A⊔B:Subgroup K)=6) :
    B⊓normalizer (A:Set K)=⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  by_contra hzne
  change z≠1 at hzne
  have hBN:B≤normalizer (A:Set K) := by
    intro b hb
    by_cases hb1:b=1
    · simpa only [hb1] using (normalizer (A:Set K)).one_mem
    obtain ⟨y,_,hy⟩:=(Nat.card_eq_two_iff' (1:B)).mp hB
    have hbne:(⟨b,hb⟩:B)≠1:=fun he=>hb1 (congrArg Subtype.val he)
    have hzne':(⟨z,hz.1⟩:B)≠1:=fun he=>hzne (congrArg Subtype.val he)
    have he:b=z:=congrArg Subtype.val ((hy _ hbne).trans (hy _ hzne').symm)
    exact he ▸ hz.2
  have hpA:IsPGroup 2 A:=IsPGroup.of_card (n:=1) (by simpa only [pow_one] using hA)
  have hpB:IsPGroup 2 B:=IsPGroup.of_card (n:=1) (by simpa only [pow_one] using hB)
  obtain ⟨n,hn⟩:=IsPGroup.iff_card.mp (hpA.to_sup_of_normal_left' hpB hBN)
  rw [hAB] at hn
  have hd:3∣2^n:=hn ▸ (by decide : 3∣6)
  exact (by decide : ¬3∣2) (Nat.Prime.dvd_of_dvd_pow (by decide) hd)

variable {G:Type*} [Group G]
open scoped commutatorElement

theorem mem_kernel_of_commutators_of_six_image (f:G→*K) (A B:Subgroup G)
    (hA:Nat.card (A.map f)=2) (hB:Nat.card (B.map f)=2)
    (hAB:Nat.card ((A⊔B).map f)=6) (z:G) (hz:z∈B)
    (hcomm:∀a∈A,⁅a,z⁆∈f.ker) : z∈f.ker := by
  have hc:f z∈centralizer (A.map f:Set K) := by
    rintro _ ⟨a,ha,rfl⟩
    have hh:=hcomm a ha
    change f ⁅a,z⁆=1 at hh
    rw [map_commutatorElement] at hh
    exact commutatorElement_eq_one_iff_mul_comm.mp hh
  have hn:f z∈normalizer (A.map f:Set K):=centralizer_le_normalizer _ hc
  have he:=second_inf_normalizer_eq_bot_of_six (A.map f) (B.map f) hA hB
    (by rwa [←map_sup])
  have hm:f z∈B.map f⊓normalizer (A.map f:Set K):=⟨mem_map_of_mem f hz,hn⟩
  rwa [he,mem_bot] at hm
end Subgroup
