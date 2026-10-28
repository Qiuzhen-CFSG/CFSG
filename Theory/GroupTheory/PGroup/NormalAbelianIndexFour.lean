module

public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Abelian normal subgroups of index at most four

If a finite group contains an elementary sixteen and a normal abelian subgroup
`D` of index at most four whose omega subgroup has order at most four, then
`B ∩ D = Ω₁(D)` has order four and `B D` is the whole group. Both factors
centralize this intersection, so it is central. A group with only one central
involution cannot have this configuration.

In the absence of normal elementary eights, the omega bound is automatic.
This excludes the homocyclic-base alternatives 1.4(a,b) in Janko–Thompson,
Math. Z. 113 (1970), printed p.386, in the final paragraph of p.395. The
argument is intrinsic and does not assume the MacWilliams classification.
-/

namespace Subgroup

/-- An elementary sixteen fills the quotient by a normal abelian subgroup of
index at most four and centralizes its whole omega four. -/
public theorem omega_one_four_central_of_elementary_sixteen {P : Type*} [Group P] [Finite P]
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hi : D.index ≤ 4) (ho : Nat.card (omega₁ D (p := 2)) ≤ 4)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hb : Nat.card B = 16) :
    Nat.card (omega₁ D (p := 2)) = 4 ∧
      (omega₁ D (p := 2)).map D.subtype ≤ center P := by
  let O := (omega₁ D (p := 2)).map D.subtype
  have hOD : O ≤ D := map_subtype_le _
  have hIO : B ⊓ D ≤ O := by
    intro x hx
    refine ⟨⟨x, hx.2⟩, subset_closure ?_, rfl⟩
    change (⟨x, hx.2⟩ : D) ^ (2 ^ 1) = 1
    apply Subtype.ext
    simpa using elemPow_eq_one_of_isElementaryAbelian x hx.1
  have hO : Nat.card O ≤ 4 := by
    rwa [card_map_of_injective D.subtype_injective]
  have hI : Nat.card (B ⊓ D : Subgroup P) ≤ 4 :=
    (card_le_of_le hIO).trans hO
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes D B
    (show B ≤ normalizer (D : Set P) from le_normalizer_of_normal)
  rw [inf_comm D B, sup_comm D B, hb] at hprod
  have hDpos := Nat.card_pos (α := D)
  have hsup := (B ⊔ D : Subgroup P).card_le_card_group
  have hi' := D.card_mul_index
  have hP : Nat.card P ≤ Nat.card D * 4 := by
    rw [← hi']
    exact Nat.mul_le_mul_left _ hi
  have hIfour : Nat.card (B ⊓ D : Subgroup P) = 4 := by
    have hh := Nat.mul_le_mul_left (Nat.card (B ⊓ D : Subgroup P)) (hsup.trans hP)
    rw [← hprod] at hh
    nlinarith
  have hOeq : Nat.card O = 4 := by
    have hh := card_le_of_le hIO
    omega
  have hIOeq : B ⊓ D = O := eq_of_le_of_card_ge hIO (by omega)
  have hOB : O ≤ B := hIOeq ▸ inf_le_left
  have hsup_eq : B ⊔ D = ⊤ := by
    apply eq_top_of_card_eq
    rw [hIfour] at hprod
    nlinarith
  have hBC : B ≤ centralizer (O : Set P) := by
    intro b hb o ho
    exact congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨o, hOB ho⟩ : B) (⟨b, hb⟩ : B))
  have hDC : D ≤ centralizer (O : Set P) := by
    intro d hd o ho
    exact congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨o, hOD ho⟩ : D) (⟨d, hd⟩ : D))
  refine ⟨?_, ?_⟩
  · rwa [card_map_of_injective D.subtype_injective] at hOeq
  · intro o ho
    apply mem_center_iff.mpr
    intro x
    have hx : x ∈ B ⊔ D := by rw [hsup_eq]; trivial
    exact ((sup_le hBC hDC hx) o ho).symm

/-- With only one central involution, a rank-two abelian normal subgroup of
index at most four prevents elementary subgroups of order sixteen. -/
public theorem no_elementary_sixteen_of_abelian_index_four {P : Type*} [Group P] [Finite P]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hi : D.index ≤ 4) (ho : Nat.card (omega₁ D (p := 2)) ≤ 4)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hb : Nat.card B = 16) : False := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hfour, hcentral⟩ := omega_one_four_central_of_elementary_sixteen D hi ho B hb
  let O := (omega₁ D (p := 2)).map D.subtype
  let : IsElementaryAbelian 2 (omega₁ D (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative D
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.map_subtype
  have hle : O ≤ (omega₁ (center P) (p := 2)).map (center P).subtype := by
    intro o ho
    refine ⟨⟨o, hcentral ho⟩, subset_closure ?_, rfl⟩
    change (⟨o, hcentral ho⟩ : center P) ^ (2 ^ 1) = 1
    apply Subtype.ext
    simpa using elemPow_eq_one_of_isElementaryAbelian o ho
  have hc := card_le_of_le hle
  rw [card_map_of_injective D.subtype_injective,
    card_map_of_injective (center P).subtype_injective, hfour, hZ] at hc
  omega

/-- The omega subgroup of a normal abelian subgroup has order at most four
when there is no normal elementary subgroup of order at least eight. -/
public theorem card_omega_one_le_four_of_normal_abelian_of_no_normal_eight {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D] :
    Nat.card (omega₁ D (p := 2)) ≤ 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O := omega₁ D (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative D
  let K := O.map D.subtype
  have hKn : K.Normal := ConjAct.normal_of_characteristic_of_normal
  have hKe : IsElementaryAbelian 2 K := IsElementaryAbelian.map_subtype
  have hlt : Nat.card O < 8 := by
    by_contra! h
    apply hno ⟨K, hKn, hKe, ?_⟩
    simpa only [K, card_map_of_injective D.subtype_injective] using h
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 O).exists_card_eq
  have hnlt : n < 3 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    simpa [← hn] using hlt
  change Nat.card O ≤ 4
  interval_cases n <;> simp_all

/-- An elementary sixteen and a unique central involution force every normal
abelian subgroup to have index greater than four, provided normal elementary
eights are absent. -/
public theorem four_lt_index_of_normal_abelian_of_elementary_sixteen
    {P : Type*} [Group P] [Finite P]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D] : 4 < D.index := by
  by_contra! hi
  exact no_elementary_sixteen_of_abelian_index_four hZ D hi
    (card_omega_one_le_four_of_normal_abelian_of_no_normal_eight hno D) B hB

end Subgroup
