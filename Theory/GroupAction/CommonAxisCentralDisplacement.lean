module
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# Actions fixing a subgroup of index two

Evaluation at an element outside the fixed subgroup determines each actor.
If every displacement lies in a marked subgroup, this evaluation embeds the
faithful action image into that subgroup. The original 14.3.19(2) consumer
uses a common fixed hyperplane and a central axis of order two.
Source: Aschbacher--Smith, Quasithin Groups, 14.3.19(2), printed p.997.
-/

@[expose] public noncomputable section
open Subgroup
namespace MulAut
variable {V A : Type*} [Group V] [Group A] [Finite V]

theorem card_range_le_of_fixed_index_two_displacement
    (ρ : A →* MulAut V) (C Z : Subgroup V) (hi : C.index=2)
    (hf : ∀ a : A, ∀ x∈C, ρ a x=x)
    (hd : ∀ a : A, ∀ x : V, x⁻¹*ρ a x∈Z) :
    Nat.card ρ.range≤Nat.card Z := by
  have hC : C≠⊤ := by
    intro he
    rw [he, index_top] at hi
    omega
  obtain ⟨x,hx⟩ := SetLike.exists_not_mem_of_ne_top C hC
  let f : ρ.range → Z := fun a=>⟨x⁻¹*a.val x, by
    obtain ⟨b,hb⟩ := a.property
    rw [←hb]
    exact hd b x⟩
  apply Nat.card_le_card_of_injective f
  intro a b he
  apply Subtype.ext
  apply MulEquiv.ext
  intro y
  obtain ⟨a',ha⟩ := a.property
  obtain ⟨b',hb⟩ := b.property
  have heval : a.val x=b.val x := by
    have hh := congrArg Subtype.val he
    change x⁻¹*a.val x=x⁻¹*b.val x at hh
    exact mul_left_cancel hh
  by_cases hy : y∈C
  · rw [←ha,←hb,hf a' y hy,hf b' y hy]
  · have hxy : x⁻¹*y∈C := by
      rw [C.mul_mem_iff_of_index_two hi,inv_mem_iff]
      exact iff_of_false hx hy
    have hya : a.val (x⁻¹*y)=x⁻¹*y := by rw [←ha];exact hf a' _ hxy
    have hyb : b.val (x⁻¹*y)=x⁻¹*y := by rw [←hb];exact hf b' _ hxy
    calc
      a.val y=a.val (x*(x⁻¹*y)) := by rw [mul_inv_cancel_left]
      _=a.val x*(x⁻¹*y) := by rw [map_mul,hya]
      _=b.val x*(x⁻¹*y) := by rw [heval]
      _=b.val (x*(x⁻¹*y)) := by rw [map_mul,hyb]
      _=b.val y := by rw [mul_inv_cancel_left]

end MulAut

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem conjugation_card_le_two_of_fixed_hyperplane
    (A D C Z : Subgroup G) (hDA : D≤normalizer (A:Set G))
    (hCA : C≤A) (hZA : Z≤A) (hAc : Nat.card A=16)
    (hCc : Nat.card C=8) (hZc : Nat.card Z=2)
    (hfix : D≤centralizer (C:Set G)) (hcomm : ⁅A,D⁆≤Z) :
    Nat.card (A.normalizerMonoidHom.comp (inclusion hDA)).range≤2 := by
  let ρ := A.normalizerMonoidHom.comp (inclusion hDA)
  have hc : Nat.card (C.subgroupOf A)=8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCA).toEquiv).trans hCc
  have hz : Nat.card (Z.subgroupOf A)=2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv).trans hZc
  have hi : (C.subgroupOf A).index=2 := by
    have hh := (C.subgroupOf A).card_mul_index
    rw [hc,hAc] at hh
    omega
  have hf (d : D) (x : A) (hx : x∈C.subgroupOf A) : ρ d x=x := by
    apply Subtype.ext
    change (A.normalizerMonoidHom ⟨d,hDA d.property⟩ x:G)=(x:G)
    rw [normalizerMonoidHom_apply_apply_coe]
    have hh := (mem_centralizer_iff.mp (hfix d.property)) (x:G) hx
    rw [←hh,mul_inv_cancel_right]
  have hd (d : D) (x : A) : x⁻¹*ρ d x∈Z.subgroupOf A := by
    change (x:G)⁻¹*(A.normalizerMonoidHom ⟨d,hDA d.property⟩ x:G)∈Z
    rw [normalizerMonoidHom_apply_apply_coe]
    have hh := hcomm (commutator_mem_commutator (A.inv_mem x.property) d.property)
    simpa only [commutatorElement_def,inv_inv,mul_assoc] using hh
  have hh := MulAut.card_range_le_of_fixed_index_two_displacement ρ
    (C.subgroupOf A) (Z.subgroupOf A) hi hf hd
  exact hz ▸ hh
end Subgroup
