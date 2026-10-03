module
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProductOrder
public import Theory.GroupTheory.PGroup.LargeHallRotationStructure

/-!
# Centers of large Hall rotation products

An extraspecial factor of order eight meets a nontrivial commuting normal
cyclic factor in its center of order two. Their product therefore has the
cyclic factor as its center and center index four. Apply this to the Hall
rotations, using the intrinsic fourth-power description of their product.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, Case 1, printed p.392.
-/

open Subgroup
namespace Subgroup

/-- The product of an extraspecial eight and a commuting cyclic normal subgroup
has that cyclic subgroup as center and center index four. -/
public theorem cyclic_center_index_four_of_extraspecial_cyclic_product
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (A R : Subgroup P) [A.Normal] [R.Normal]
    [IsExtraspecial 2 A] [IsCyclic R] (hA : Nat.card A = 8)
    (hR : R ≠ ⊥) (hc : R ≤ centralizer (A : Set P)) :
    IsCyclic (center (A ⊔ R : Subgroup P)) ∧
      (center (A ⊔ R : Subgroup P)).index = 4 ∧
      Nat.card (center (A ⊔ R : Subgroup P)) = Nat.card R := by
  let M := A ⊔ R
  have hi := card_inf_eq_two_of_extraspecial_of_cyclic_center hP A R hR hc
  have hinf : A ⊓ R = (center A).map A.subtype := by
    apply eq_of_le_of_card_ge
    · rintro x ⟨ha, hr⟩
      exact ⟨⟨x, ha⟩, mem_center_iff.mpr
        (fun a => Subtype.ext (hc hr a a.property)), rfl⟩
    · rw [card_map_of_injective A.subtype_injective,
        IsExtraspecial.center_order_p 2 A, hi]
  have hZ : (center M).map M.subtype = R := by
    apply le_antisymm
    · rintro x ⟨x, hx, rfl⟩
      obtain ⟨a, ha, r, hr, he⟩ := mem_sup_of_normal_right.mp x.property
      have haZ : a ∈ (center A).map A.subtype := by
        refine ⟨⟨a, ha⟩, mem_center_iff.mpr ?_, rfl⟩
        intro b
        apply Subtype.ext
        apply mul_right_cancel (b := r)
        have hh := congrArg (fun m : M => (m : P))
          (mem_center_iff.mp hx (⟨b, mem_sup_left b.property⟩ : M))
        change (b : P) * (x : P) = (x : P) * b at hh
        rw [← he] at hh
        calc
          (b : P) * a * r = (b : P) * (a * r) := mul_assoc _ _ _
          _ = (a * r) * b := hh
          _ = a * b * r := by rw [mul_assoc, ← hc hr b b.property, ← mul_assoc]
      change (x : P) ∈ R
      rw [← he]
      exact R.mul_mem (show a ∈ R from (hinf.symm ▸ haZ : a ∈ A ⊓ R).2) hr
    · intro r hr
      refine ⟨⟨r, mem_sup_right hr⟩, mem_center_iff.mpr ?_, rfl⟩
      intro x
      apply Subtype.ext
      have hle : M ≤ centralizer ({r} : Set P) := by
        apply sup_le
        · intro a ha
          exact mem_centralizer_singleton_iff.mpr (hc hr a ha)
        · intro b hb
          exact mem_centralizer_singleton_iff.mpr (R.le_centralizer hr b hb)
      exact mem_centralizer_singleton_iff.mp (hle x.property)
  let e : center M ≃* R :=
    ((center M).equivMapOfInjective M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr hZ)
  have hcard : Nat.card (center M) = Nat.card R := Nat.card_congr e.toEquiv
  refine ⟨e.isCyclic.mpr inferInstance, ?_, hcard⟩
  have hmul := card_mul_eq_card_inf_mul_card_sup_of_normalizes A R
    (hc.trans (centralizer_le_normalizer _))
  rw [hi, hA] at hmul
  have hidx := (center M).card_mul_index
  rw [hcard] at hidx
  have hpos : 0 < Nat.card R := Nat.card_pos
  change 8 * Nat.card R = 2 * Nat.card M at hmul
  nlinarith
/-- The intrinsic rotation product for an extraspecial eight and a large Hall
tail is characteristic and has cyclic center of index four and order at least eight. -/
public theorem intrinsic_rotation_center_of_large_hall
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (A D : Subgroup P) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (A : Set P)) (hg : A ⊔ D = ⊤)
    (hlarge : 16 ≤ Nat.card D) :
    (closure {x : P | x ^ 4 ≠ 1}).Characteristic ∧
      IsCyclic (center (closure {x : P | x ^ 4 ≠ 1})) ∧
      (center (closure {x : P | x ^ 4 ≠ 1})).index = 4 ∧
      8 ≤ Nat.card (center (closure {x : P | x ^ 4 ≠ 1})) := by
  obtain ⟨R, hRc, hRcyc, hR, hout, _⟩ :=
    IsBinaryHallFactor.exists_characteristic_large_rotation (hP.to_subgroup D) hD hn hlarge
  let : R.Characteristic := hRc
  let : IsCyclic R := hRcyc
  let B := R.map D.subtype
  let : B.Normal := inferInstance
  let : IsCyclic B := (R.equivMapOfInjective D.subtype D.subtype_injective).isCyclic.mp
    inferInstance
  have hB : 8 ≤ Nat.card B := by
    rw [show Nat.card B = Nat.card R from card_map_of_injective D.subtype_injective]
    exact hR
  have hBD : B ≤ D := map_subtype_le R
  have houtB (d : P) (hd : d ∈ D) (hnB : d ∉ B) : d ^ 4 = 1 := by
    exact congrArg Subtype.val (hout ⟨d, hd⟩ (fun h => hnB ⟨⟨d, hd⟩, h, rfl⟩))
  have hAp (a : P) (ha : a ∈ A) : a ^ 4 = 1 :=
    congrArg Subtype.val (IsExtraspecial.pow_four_eq_one (⟨a, ha⟩ : A))
  have hM := sup_eq_closure_nontrivial_fourth_powers A D B hAp hc hg hBD hB houtB
  rw [← hM]
  obtain ⟨hcyc, hi, hz⟩ := cyclic_center_index_four_of_extraspecial_cyclic_product
    hP A B hA (by intro he; simp [he] at hB) (hBD.trans hc)
  exact ⟨characteristic_sup_of_fourth_power_rotation A D B hAp hc hg hBD hB houtB,
    hcyc, hi, hz.symm ▸ hB⟩

end Subgroup
