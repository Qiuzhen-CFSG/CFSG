module

import all Theory.SpecificGroups.PSL2.QuinticInnerFusion
public import Theory.SpecificGroups.PSL2.QuinticLinearFusion

/-!
# Capturing the linear part of a quintic two-core

Inside a normal subgroup embedded in odd PGL₂, the intersection with the
original quintic two-core has no Klein four: it centralizes the quintic
subgroup. Its unique involution is fixed by the whole supplied Sylow.
The self-centralizing property of a Klein four inside that linear subgroup
then captures every elementary subgroup of this core intersection.

This is the field-trivial row of the simultaneous fusion argument in
Aschbacher--Smith 6.1.4, printed p.666.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- The elementary part of the actual quintic core in a normal linear
subgroup lies in each Klein four of that linear subgroup inside the Sylow. -/
theorem odd_quintic_linear_core_le_four
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (H : Subgroup G) [H.Normal] (f : H →* PGL2 F) (hfi : Function.Injective f)
    (T : Sylow 2 G) (X : Subgroup G) (hXH : X ≤ H) (hfive : Nat.card X = 5)
    (hTX : (T : Subgroup G) ≤ normalizer X)
    (V : Subgroup G) (hV : IsKleinFour V) (hVT : V ≤ (T : Subgroup G)) (hVH : V ≤ H)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAS : A ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2) (hAH : A ≤ H) : A ≤ V := by
  classical
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_cases hAb : A = ⊥
  · rw [hAb]; exact bot_le
  let B := X ⊔ (T : Subgroup G)
  let S := B.pCoreIn 2
  let R := S ⊓ H
  let i : R →* H := inclusion inf_le_right
  let r := f.comp i
  have hri : Function.Injective r := hfi.comp (inclusion_injective inf_le_right)
  let Y := (X.subgroupOf H).map f
  have hYcard : Nat.card Y = 5 := by
    rw [card_map_of_injective hfi, Nat.card_congr (subgroupOfEquivOfLe hXH).toEquiv]
    exact hfive
  let : IsCyclic Y := isCyclic_of_prime_card hYcard
  have hYne : Y ≠ ⊥ := by intro he; simp [he] at hYcard
  have hYodd : Odd (Nat.card Y) := by rw [hYcard]; decide
  have hSC : S ≤ centralizer (X : Set G) := quintic_join_core_centralizes X T hfive hTX
  have hno (W : Subgroup R) (hW : IsElementaryAbelian 2 W) (hc : Nat.card W = 4) : False := by
    let : IsElementaryAbelian 2 W := hW
    let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have hWK : IsKleinFour W := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
    have hWC : W.map r ≤ centralizer (Y : Set (PGL2 F)) := by
      rintro _ ⟨w, hw, rfl⟩ y ⟨x, hx, rfl⟩
      have hh : x * i w = i w * x := Subtype.ext (hSC w.property.1 x hx)
      have he := congrArg f hh
      simpa only [r, MonoidHom.comp_apply, map_mul] using he
    exact pgl2_no_kleinFour_centralizes_odd_cyclic F hF Y (W.map r) inferInstance hYne hYodd
      (isKleinFour_map_of_injective W hWK r hri) hWC
  let : IsElementaryAbelian 2 A := hA
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hAb
  obtain ⟨a, ha, ha1⟩ := A.exists_ne_one_of_nontrivial
  have haR : a ∈ R := ⟨hAS ha, hAH ha⟩
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr (by
    intro he
    exact ha1 (mem_bot.mp (he ▸ haR)))
  have hRp : IsPGroup 2 R := (isPGroup_pCoreIn 2 B).to_le inf_le_left
  obtain ⟨z, _, _, huniq⟩ := hRp.exists_central_involution_of_no_elementary_four hno
  have haz : (⟨a, haR⟩ : R) = z := (huniq ⟨a, haR⟩ (Subtype.ext ha2)).resolve_left
    (fun he => ha1 (congrArg Subtype.val he))
  have hAcyc : A = zpowers a := by
    apply le_antisymm _ (zpowers_le.mpr ha)
    intro b hb
    rcases huniq ⟨b, hAS hb, hAH hb⟩ (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian b hb)) with he | he
    · have hb1 : b = 1 := congrArg Subtype.val he
      simpa only [hb1] using one_mem (zpowers a)
    · have hba : b = a := congrArg Subtype.val (he.trans haz.symm)
      simpa only [hba] using mem_zpowers a
  have hTS : (T : Subgroup G) ≤ normalizer S :=
    (show (T : Subgroup G) ≤ B from le_sup_right).trans
      (B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hTa (t : G) (ht : t ∈ (T : Subgroup G)) : t * a * t⁻¹ = a := by
    have hm : t * a * t⁻¹ ∈ R :=
      ⟨(mem_normalizer_iff.mp (hTS ht) a).mp haR.1, (inferInstance : H.Normal).conj_mem a haR.2 t⟩
    have hs : (t * a * t⁻¹) ^ 2 = 1 := by
      change (MulAut.conj t a) ^ 2 = 1
      rw [← map_pow, ha2, map_one]
    have hn : t * a * t⁻¹ ≠ 1 := fun he => ha1
      ((MulAut.conj t).injective (he.trans (map_one _).symm))
    have he := (huniq ⟨t * a * t⁻¹, hm⟩ (Subtype.ext hs)).resolve_left
      (fun he => hn (congrArg Subtype.val he))
    exact congrArg Subtype.val (he.trans haz.symm)
  let V' := (V.subgroupOf H).map f
  have hV' : IsKleinFour V' := isKleinFour_map_of_injective (V.subgroupOf H)
    (isKleinFour_subgroupOf hVH hV) f hfi
  have haV' : f ⟨a, hAH ha⟩ ∈ V' := by
    rw [← pgl2_kleinFour_centralizer_eq_self F hF V' hV']
    rintro v ⟨w, hw, rfl⟩
    have hh : w * (⟨a, hAH ha⟩ : H) = ⟨a, hAH ha⟩ * w :=
      Subtype.ext (mul_inv_eq_iff_eq_mul.mp (hTa w (hVT hw)))
    simpa only [map_mul] using congrArg f hh
  obtain ⟨v, hv, he⟩ := haV'
  have hva : (v : G) = a := congrArg Subtype.val (hfi he)
  rw [hAcyc]
  exact zpowers_le.mpr (hva ▸ hv)

end Theory.PSL2
