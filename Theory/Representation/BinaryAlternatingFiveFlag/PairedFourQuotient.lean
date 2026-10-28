module
public import Theory.Representation.BinaryAlternatingFiveFlag.PairedFour
public import Stellmacher.SectionsOneToFourDefs

/-!
# Irreducibility on a literal paired four-group quotient

A surjection from the actual upper subgroup records the two regular four-group
coordinates and its exact lower kernel. Independent alternating point-stabilizer
lifts and an element exchanging the two factor preimages force every invariant
subgroup in that interval to be one endpoint. All conjugations are by elements
of the stated actor; no larger Sylow action is required.

Source application: Aschbacher--Smith, 14.6.9(l), printed p.1027, on
O₂(I ∩ Mc)/O₂(I) with actor I ∩ Mc.
-/

@[expose] public section

open Subgroup
namespace BinaryPermutation.AlternatingFiveFlag
open AlternatingFiveBorel
variable {G : Type*} [Group G]

/-- Marked independent actors and factor exchange on an actual quotient. -/
structure PairedFourQuotient (J A C : Subgroup G) where
  q : C →* four × four
  surjective : Function.Surjective q
  kernel : q.ker.map C.subtype = A
  normalizes : J ≤ normalizer (C : Set G)
  first_actor : ∀ b : B, ∃ g : J, ∀ x : C,
    q ⟨(g : G) * x * (g : G)⁻¹, (normalizes g.property x).mp x.property⟩ =
      (fourConj b (q x).1, (q x).2)
  second_actor : ∀ b : B, ∃ g : J, ∀ x : C,
    q ⟨(g : G) * x * (g : G)⁻¹, (normalizes g.property x).mp x.property⟩ =
      ((q x).1, fourConj b (q x).2)
  exchange : ∃ t : J,
    ((((⊤ : Subgroup four).prod ⊥).comap q).map C.subtype).map
        (MulAut.conj (t : G)).toMonoidHom =
      (((⊥ : Subgroup four).prod ⊤).comap q).map C.subtype

namespace PairedFourQuotient
variable {J A C : Subgroup G}

/-- Pull the paired four-group geometry back through the actual quotient map. -/
theorem irreducible (d : PairedFourQuotient J A C) :
    Stellmacher.IsIrreducibleSection J A C := by
  have hAC : A ≤ C := d.kernel ▸ map_subtype_le d.q.ker
  refine ⟨hAC, ?_, ?_⟩
  · intro he
    have hqone (x : C) : d.q x = 1 := by
      have hx : (x : G) ∈ A := he.symm ▸ x.property
      rw [←d.kernel] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hexy : y = x := Subtype.ext hyx
      exact hexy ▸ hy
    have hf : ∀ x : four × four, x = 1 := by
      intro x
      obtain ⟨y,rfl⟩ := d.surjective x
      exact hqone y
    let : Subsingleton four := ⟨fun x y => by
      have hx := congrArg Prod.fst (hf (x,1))
      have hy := congrArg Prod.fst (hf (y,1))
      exact hx.trans hy.symm⟩
    have hc : Nat.card four = 1 := Nat.card_of_subsingleton (1 : four)
    rw [four_card] at hc
    omega
  · intro W hAW hWC hi
    let U := (W.subgroupOf C).map d.q
    have hker : d.q.ker ≤ W.subgroupOf C := by
      intro x hx
      exact hAW (d.kernel ▸ mem_map_of_mem C.subtype hx)
    have hpull : U.comap d.q = W.subgroupOf C := by
      dsimp only [U]
      rw [comap_map_eq_self hker]
    have hl : ∀ b : B, ∀ x ∈ U, (fourConj b x.1,x.2) ∈ U := by
      intro b x hx
      obtain ⟨g,hg⟩ := d.first_actor b
      obtain ⟨y,hy,rfl⟩ := hx
      rw [←hg y]
      exact mem_map_of_mem d.q (hi g y hy)
    have hr : ∀ b : B, ∀ x ∈ U, (x.1,fourConj b x.2) ∈ U := by
      intro b x hx
      obtain ⟨g,hg⟩ := d.second_actor b
      obtain ⟨y,hy,rfl⟩ := hx
      rw [←hg y]
      exact mem_map_of_mem d.q (hi g y hy)
    have hWn : J ≤ normalizer (W : Set G) := by
      intro g hg
      apply mem_normalizer_iff.mpr
      intro w
      constructor
      · exact hi ⟨g,hg⟩ w
      · intro hw
        have hh := hi ⟨g⁻¹,J.inv_mem hg⟩ (g*w*g⁻¹) hw
        simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,
          inv_mul_cancel,mul_one] using hh
    have hf (P : Subgroup (four × four)) :
        P ≤ U ↔ (P.comap d.q).map C.subtype ≤ W := by
      rw [map_le_iff_le_comap]
      change P ≤ U ↔ P.comap d.q ≤ W.subgroupOf C
      rw [←hpull]
      exact (comap_le_comap_of_surjective d.surjective).symm
    have hex : (⊤ : Subgroup four).prod ⊥ ≤ U ↔
        (⊥ : Subgroup four).prod ⊤ ≤ U := by
      rw [hf,hf]
      obtain ⟨t,ht⟩ := d.exchange
      have htW : W.map (MulAut.conj (t : G)).toMonoidHom = W :=
        mem_normalizer_iff_map_conj_eq.mp (hWn t.property)
      constructor
      · intro hh
        have hm := map_mono (f := (MulAut.conj (t : G)).toMonoidHom) hh
        rwa [ht,htW] at hm
      · intro hh
        apply (map_le_map_iff_of_injective (f := (MulAut.conj (t : G)).toMonoidHom)
          (MulAut.conj (t : G)).injective).mp
        rwa [ht,htW]
    rcases pair_four_irreducible_of_factor_exchange U hl hr hex with hU | hU
    · left
      apply le_antisymm _ hAW
      intro w hw
      have hwU : d.q ⟨w,hWC hw⟩ ∈ U := mem_map_of_mem d.q hw
      have hwker : (⟨w,hWC hw⟩ : C) ∈ d.q.ker := by
        change d.q ⟨w,hWC hw⟩ = 1
        exact show d.q ⟨w,hWC hw⟩ ∈ (⊥ : Subgroup (four × four)) from hU ▸ hwU
      exact d.kernel ▸ mem_map_of_mem C.subtype hwker
    · right
      apply le_antisymm hWC
      intro w hw
      have hh : (⟨w,hw⟩ : C) ∈ U.comap d.q := hU.symm ▸ mem_top _
      exact show (⟨w,hw⟩ : C) ∈ W.subgroupOf C from hpull ▸ hh

end PairedFourQuotient
end BinaryPermutation.AlternatingFiveFlag
