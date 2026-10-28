module
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# Cubic pairs in the normalizer of a sixteen-subgroup

Two commuting cyclic subgroups with trivial intersection embed their direct
product in any common overgroup. If the first order is divisible by three
and the second is three, nine divides the overgroup order. For the normalizer
of a subgroup of order sixteen, this divisor survives in the normalizer
quotient because nine and sixteen are coprime.

Source application: the two elementary-sixteen groups in Aschbacher–Smith
F.5.5, printed p.302. The first ambient actor need not itself have order three.
-/
@[expose] public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]
theorem nine_dvd_normalizer_quotient_of_disjoint_cubics
    (B : Subgroup G) (hB : Nat.card B=16) (x y : G)
    (hxN : x∈normalizer (B : Set G)) (hyN : y∈normalizer (B : Set G))
    (hxy : Commute x y) (hdis : Disjoint (zpowers x) (zpowers y))
    (hx3 : 3 ∣ orderOf x) (hy3 : orderOf y=3) :
    9 ∣ Nat.card (normalizer (B : Set G) ⧸ B.subgroupOf (normalizer (B : Set G))) := by
  let N := normalizer (B : Set G)
  have hX : zpowers x ≤ N := zpowers_le.mpr hxN
  have hY : zpowers y ≤ N := zpowers_le.mpr hyN
  have hc : ∀ a : zpowers x, ∀ b : zpowers y, Commute (a:G) (b:G) := by
    intro a b
    obtain ⟨m,hm⟩ := mem_zpowers_iff.mp a.property
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp b.property
    rw [←hm,←hn]
    exact (hxy.zpow_left m).zpow_right n
  let f := (zpowers x).subtype.noncommCoprod (zpowers y).subtype hc
  have hf : Function.Injective f := mul_injective_of_disjoint hdis
  let fN : (zpowers x × zpowers y) →* N := f.codRestrict N (by
    intro a
    exact N.mul_mem (hX a.1.property) (hY a.2.property))
  have hi : Function.Injective fN := by
    intro a b hab
    exact hf (congrArg Subtype.val hab)
  have hd := card_dvd_of_injective fN hi
  rw [Nat.card_prod,Nat.card_zpowers,Nat.card_zpowers,hy3] at hd
  have h9N : 9 ∣ Nat.card N := (Nat.mul_dvd_mul_right hx3 3).trans hd
  have hcard : Nat.card (B.subgroupOf N)=16 :=
    (Nat.card_congr (subgroupOfEquivOfLe B.le_normalizer).toEquiv).trans hB
  have he := (B.subgroupOf N).card_mul_index
  rw [hcard,index_eq_card] at he
  rw [←he] at h9N
  exact (show Nat.Coprime 9 16 by decide).dvd_of_dvd_mul_left h9N
end Subgroup
