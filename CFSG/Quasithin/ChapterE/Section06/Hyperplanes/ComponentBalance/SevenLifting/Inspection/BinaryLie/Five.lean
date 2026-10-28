module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import Theory.SpecificGroups.BinaryLinear.FiveSevenFixer
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The PSL₅(2) branch of the seven-component inspection

Transport the supplied finite field of order two and the actual projective
model to the natural binary linear group. Both A₇ and its perfect central
three-cover have order divisible by 2520, supplying a five-subgroup and a
seven-element in the embedded component. Every element of the acting
two-subgroup fixes their images. The graph obstruction and the inner
five-centralizer calculation force its automorphism order to divide fifteen,
so it is trivial.

The full common fixed subgroup and both component alternatives are retained.
The matrix argument needs no additional simplicity or rank hypotheses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252/PDF p.263, and Theorem C(4), printed p.33.
-/

open Subgroup BinaryLinear.OuterCyclic

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie

/-- The actual PSL₅(2) model has no seven-component fixed by a nontrivial
two-subgroup of automorphisms. -/
public theorem binary_five {S : Type*} [Group S] [Finite S]
    (h : ClassicalGroup.IsPSL S 5 2) : SevenActionInspection S := by
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := h
  let _ : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let e : S ≃* LinearGroup 5 :=
    (e₀.trans (Atlas.fieldEquivPSL 5 eF)).trans (projectiveEquivLinear (by decide))
  intro P hP L hLF _ hs
  have hcard := seven_card_dvd hs
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := L) 5 (n := 1)
    ((by decide : 5 ^ 1 ∣ 2520).trans hcard)
  let A := A₀.map L.subtype
  let B := A.map e.toMonoidHom
  have hB : Nat.card B = 5 := by
    rw [card_map_of_injective e.injective, card_map_of_injective L.subtype_injective]
    simpa using hA₀
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 7
    ((by decide : 7 ∣ 2520).trans hcard)
  have hex : orderOf (e x.val) = 7 := by
    rw [e.orderOf_eq, Subgroup.orderOf_coe x, hx]
  apply eq_bot_iff.mpr
  intro a ha
  let aP : P := ⟨a, ha⟩
  let b := MulAut.congr e a
  have hfix : ∀ y ∈ B, b y = y := by
    rintro _ ⟨y, hy, rfl⟩
    have hyL : y ∈ L := map_subtype_le A₀ hy
    have hf : a y = y := hLF hyL aP
    change e (a (e.symm (e _))) = e _
    rw [e.symm_apply_apply, hf]
  have hxfix : b (e x.val) = e x.val := by
    have hf : a x.val = x.val := hLF x.property aP
    change e (a (e.symm (e _))) = e _
    rw [e.symm_apply_apply, hf]
  have hd := BinaryLinear.FiveSevenFixer.order_dvd_fifteen B hB (e x.val) hex b hfix hxfix
  have hord : orderOf b = orderOf aP :=
    ((MulAut.congr e).orderOf_eq a).trans (Subgroup.orderOf_coe aP)
  rw [hord] at hd
  have hone : aP = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes
      (hP.orderOf_coprime (by decide : Nat.Coprime 2 15) aP) dvd_rfl hd)
  exact congrArg Subtype.val hone

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
