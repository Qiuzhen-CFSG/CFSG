module

public import Theory.GroupTheory.PGroup.NormalEightFour

/-!
# Characteristic subgroups of the centralizer of a normal four

Let `W` be a normal elementary four in a finite group with no normal
elementary subgroup of order at least eight. The first omega subgroup of
the center of `C(W)` is exactly `W`. Characteristic elementary subgroups of
`C(W)` cannot have order at least eight, since their images are normal in
the original group. This does not bound all normal elementary subgroups
of `C(W)`.

If automorphisms of `C(W)` are transitive on the involutions of `W`, then
`C(W)` has no characteristic subgroup of order two. Such a subgroup would
be normal in the original group, hence central and contained in `W`;
transitivity contradicts its characteristicity.

These are intrinsic reductions for the fusion argument in Janko–Thompson,
Math. Z. 113 (1970), §6, printed p.395, toward the structure cited in 1.4.
-/

open Subgroup

namespace Subgroup

/-- The normal-eight obstruction descends to characteristic elementary
subgroups of a normal subgroup. It need not descend to normal subgroups. -/
public theorem no_characteristic_elementary_eight_of_normal
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (C : Subgroup P) [C.Normal] :
    ¬ ∃ K : Subgroup C, K.Characteristic ∧ IsElementaryAbelian 2 K ∧
      8 ≤ Nat.card K := by
  rintro ⟨K, hKchar, hKel, hK⟩
  let : K.Characteristic := hKchar
  let : IsElementaryAbelian 2 K := hKel
  exact hno ⟨K.map C.subtype, ConjAct.normal_of_characteristic_of_normal,
    IsElementaryAbelian.map_subtype, by
      rwa [card_map_of_injective C.subtype_injective]⟩

/-- The central omega of the centralizer, viewed in the original group,
coincides with the given normal four. -/
public theorem omega_one_center_centralizer_eq_normal_four
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4) :
    ((omega₁ (center (centralizer (W : Set P))) (p := 2)).map
      (center (centralizer (W : Set P))).subtype).map
      (centralizer (W : Set P)).subtype = W := by
  let C := centralizer (W : Set P)
  let O := omega₁ (center C) (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let Z := O.map (center C).subtype
  let : Z.Characteristic := characteristic_of_characteristic_of_characteristic
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map_subtype
  let K := Z.map C.subtype
  let : K.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.map_subtype
  have hWK : W ≤ K := by
    intro w hw
    have hwC : w ∈ C := le_centralizer W hw
    have hwZ : (⟨w, hwC⟩ : C) ∈ center C := by
      apply mem_center_iff.mpr
      intro c
      exact Subtype.ext (c.property w hw).symm
    refine ⟨⟨w, hwC⟩, ⟨⟨⟨w, hwC⟩, hwZ⟩, subset_closure ?_, rfl⟩, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw
  have hlt : Nat.card K < 8 := by
    by_contra! h
    exact hno ⟨K, inferInstance, inferInstance, h⟩
  have hdiv : 4 ∣ Nat.card K := hW ▸ card_dvd_of_le hWK
  have hge : 4 ≤ Nat.card K := hW ▸ card_le_of_le hWK
  exact (eq_of_le_of_card_ge hWK (by omega)).symm

/-- Transitivity on a normal four forbids a characteristic subgroup of order
two in its centralizer. No bound on nonnormal elementary subgroups is used. -/
public theorem centralizer_no_characteristic_two_of_four_transitive
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y)
    (K : Subgroup (centralizer (W : Set P))) [K.Characteristic] : Nat.card K ≠ 2 := by
  classical
  let C := centralizer (W : Set P)
  intro hK
  let K₀ := K.map C.subtype
  let : K₀.Normal := ConjAct.normal_of_characteristic_of_normal
  have hK₀ : Nat.card K₀ = 2 := (card_map_of_injective C.subtype_injective).trans hK
  have hK₀W : K₀ ≤ W := by
    apply le_trans ?_ (omega_one_center_le_normal_four_of_no_normal_eight hno W hW)
    intro k hk
    have hkc := central_of_normal_card_two K₀ hK₀ hk
    refine ⟨⟨k, hkc⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    have hp : (⟨k, hk⟩ : K₀) ^ 2 = 1 := by
      rw [← hK₀]
      exact pow_card_eq_one'
    simpa using congrArg Subtype.val hp
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨z, hz⟩ := exists_ne (1 : K)
  have hzW : ((z : C) : P) ∈ W := hK₀W (mem_map_of_mem C.subtype z.property)
  have hnot : ¬ W ≤ K₀ := by
    intro h
    have hh := card_le_of_le h
    omega
  obtain ⟨x, hxW, hxK⟩ := SetLike.not_le_iff_exists.mp hnot
  let xC : C := ⟨x, le_centralizer W hxW⟩
  have hz2 : orderOf (z : C) = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hzW
    · exact fun h => hz (Subtype.ext h)
  have hx2 : orderOf xC = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hxW
    · intro h
      apply hxK
      have hx1 : x = 1 := congrArg Subtype.val h
      rw [hx1]
      exact K₀.one_mem
  obtain ⟨a, ha⟩ := htrans z xC hzW hxW hz2 hx2
  have hx : xC ∈ K := ha ▸ characteristic_iff_le_comap.mp inferInstance a z.property
  exact hxK (mem_map_of_mem C.subtype hx)

end Subgroup
