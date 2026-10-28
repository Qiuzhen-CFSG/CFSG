module

public import Theory.GroupTheory.PGroup.NormalEightCentralFour
public import Theory.GroupTheory.PGroup.CentralQuotientQuadratic
public import Theory.GroupTheory.PGroup.CriticalSubgroup

/-!
# Critical subgroups without normal elementary eights

Suppose that a finite two-group has central first omega of order four and
no normal elementary subgroup of order at least eight. Every element of a
critical subgroup lies in a normal abelian subgroup: adjoin its cyclic
subgroup to the image of the critical subgroup's center. The critical
commutator condition makes this join normal, and its two factors commute.

The first omega of that normal abelian subgroup is normal and elementary,
so it lies in the ambient central omega four. Thus all involutions in a
critical subgroup are central in the ambient group. The critical subgroup
contains the ambient center; its first omega is therefore exactly that
central four. In particular it has three involutions. Its elementary
central quotient and the existing quadratic bound give a Frattini quotient
of order at most sixteen.

This reduction does not assert centrality for involutions outside the
critical subgroup. Sources: Thompson's critical subgroup theorem,
Gorenstein, *Finite Groups*, Theorem 5.3.11; the normal-four setting of
MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3,
quoted in Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, p.386.
-/

open Subgroup
open scoped commutatorElement

namespace IsCriticalPSubgroup

/-- Every element of a critical subgroup belongs to a normal abelian subgroup inside it. -/
public theorem exists_normal_abelian_of_mem
    {P : Type*} [Group P] {p : ℕ} {C : Subgroup P}
    (hC : IsCriticalPSubgroup p C) {x : P} (hx : x ∈ C) :
    ∃ B : Subgroup P, B.Normal ∧ IsMulCommutative B ∧ x ∈ B ∧ B ≤ C := by
  let Z := (center C).map C.subtype
  let B := zpowers x ⊔ Z
  have hZC : Z ≤ centralizer (C : Set P) := by
    rw [show Z = C ⊓ centralizer (C : Set P) from map_center_subtype_eq_inf_centralizer C]
    exact inf_le_right
  have hBC : B ≤ C := sup_le (zpowers_le.mpr hx) (map_subtype_le _)
  have hZA : Z ≤ centralizer (zpowers x : Set P) :=
    hZC.trans (centralizer_le (zpowers_le.mpr hx))
  have hBn : B.Normal := commutator_top_left_le_iff.mp
    ((commutator_mono le_rfl hBC).trans (hC.commutator_le.trans le_sup_right))
  have hBa : IsMulCommutative B := le_centralizer_iff_isMulCommutative.mp
    (sup_le (le_centralizer_iff.mpr (sup_le (le_centralizer _) hZA))
      (hZC.trans (centralizer_le hBC)))
  exact ⟨B, hBn, hBa, (show zpowers x ≤ B from le_sup_left) (mem_zpowers x), hBC⟩

end IsCriticalPSubgroup

namespace Subgroup

/-- Involutions in normal abelian subgroups belong to the central omega four. -/
public theorem mem_omega_center_of_square_eq_one_of_normal_abelian
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (B : Subgroup P) [B.Normal] [IsMulCommutative B]
    {x : P} (hx : x ∈ B) (hx2 : x ^ 2 = 1) :
    x ∈ (omega₁ (center P) (p := 2)).map (center P).subtype := by
  let O := omega₁ B (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let E := O.map B.subtype
  let : E.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map_subtype
  apply normal_elementary_le_omega_center_of_no_normal_eight hno hZ E
  refine ⟨⟨x, hx⟩, subset_closure ?_, rfl⟩
  change (⟨x, hx⟩ : B) ^ (2 ^ 1) = 1
  apply Subtype.ext
  simpa using hx2

end Subgroup

namespace IsCriticalPSubgroup

/-- Involutions in a critical subgroup belong to the ambient central omega four. -/
public theorem mem_omega_center_of_square_eq_one
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    {x : P} (hx : x ∈ C) (hx2 : x ^ 2 = 1) :
    x ∈ (omega₁ (center P) (p := 2)).map (center P).subtype := by
  obtain ⟨B, hBn, hBa, hxB, _⟩ := hC.exists_normal_abelian_of_mem hx
  let : B.Normal := hBn
  let : IsMulCommutative B := hBa
  exact mem_omega_center_of_square_eq_one_of_normal_abelian hno hZ B hxB hx2

end IsCriticalPSubgroup

namespace IsCriticalPSubgroup

/-- The first omega of a critical subgroup is the ambient central omega four. -/
public theorem omega_one_map_eq_center
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4) :
    (omega₁ C (p := 2)).map C.subtype =
      (omega₁ (center P) (p := 2)).map (center P).subtype := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    apply (Subgroup.closure_le _).2
    intro x hx
    apply hC.mem_omega_center_of_square_eq_one hno hZ x.property
    simpa using congrArg Subtype.val hx
  · rintro x ⟨z, hz, rfl⟩
    have hzC : (z : P) ∈ C :=
      map_subtype_le _ (hC.centralizer_eq ▸ center_le_centralizer (C : Set P) z.property)
    refine ⟨⟨z, hzC⟩, subset_closure ?_, rfl⟩
    let : IsElementaryAbelian 2 (omega₁ (center P) (p := 2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative _
    change (⟨(z : P), hzC⟩ : C) ^ (2 ^ 1) = 1
    apply Subtype.ext
    exact congrArg (fun a : center P => (a : P))
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz)

/-- The first omega of a critical subgroup has order four. -/
public theorem card_omega_one_eq_four
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4) :
    Nat.card (omega₁ C (p := 2)) = 4 := by
  have hh := congrArg (fun H : Subgroup P => Nat.card H) (hC.omega_one_map_eq_center hno hZ)
  simpa only [card_map_of_injective C.subtype_injective,
    card_map_of_injective (center P).subtype_injective, hZ] using hh

end IsCriticalPSubgroup

namespace IsCriticalPSubgroup

/-- All involutions in a critical subgroup are central in that subgroup. -/
public theorem square_one_mem_center
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (x : C) (hx : x ^ 2 = 1) : x ∈ center C := by
  have hh := map_subtype_le _ (hC.mem_omega_center_of_square_eq_one hno hZ
    x.property (congrArg Subtype.val hx))
  exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hh y))

/-- A critical subgroup has exactly three involutions. -/
public theorem card_involutions_eq_three
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4) :
    Nat.card {x : C // orderOf x = 2} = 3 := by
  classical
  let O := omega₁ C (p := 2)
  have hpow (x : O) : (x : C) ^ 2 = 1 := by
    have hm := (hC.omega_one_map_eq_center hno hZ) ▸ mem_map_of_mem C.subtype x.property
    let : IsElementaryAbelian 2 (omega₁ (center P) (p := 2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative _
    let : IsElementaryAbelian 2 ((omega₁ (center P) (p := 2)).map (center P).subtype) :=
      IsElementaryAbelian.map_subtype
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ hm)
  let e : {x : C // orderOf x = 2} ≃ {x : O // x ≠ 1} :=
    { toFun := fun x => ⟨⟨x, subset_closure (by
        simpa using (orderOf_eq_prime_iff.mp x.property).1)⟩,
        fun h => (orderOf_eq_prime_iff.mp x.property).2 (congrArg Subtype.val h)⟩
      invFun := fun x => ⟨x.val, orderOf_eq_prime (hpow x.val)
        (fun h => x.property (Subtype.ext h))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let : Fintype O := Fintype.ofFinite O
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hc : Fintype.card O = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hC.card_omega_one_eq_four hno hZ
  simp [hc]

end IsCriticalPSubgroup

namespace IsCriticalPSubgroup

/-- The Frattini quotient of a critical subgroup has order at most sixteen. -/
public theorem card_frattini_quotient_le_sixteen_of_no_normal_eight
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4) :
    Nat.card (C ⧸ frattini C) ≤ 16 := by
  let : IsElementaryAbelian 2 (C ⧸ center C) := hC.quotient_elementary
  have hc := hC.square_one_mem_center hno hZ
  have hfour := IsPGroup.card_omega_center_eq_four_of_three_central_involutions
    hc (hC.card_involutions_eq_three hno hZ)
  have hb := (hP.to_subgroup C).card_frattini_quotient_le_sq_card_omega_center hc
  simpa only [hfour, Nat.reducePow] using hb

end IsCriticalPSubgroup
