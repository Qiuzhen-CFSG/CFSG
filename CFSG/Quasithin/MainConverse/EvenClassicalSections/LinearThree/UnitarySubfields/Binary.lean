module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import CFSG.Quasithin.MainConverse.SolvableSections
public import Theory.GroupTheory.SmallIndexSolvable
public import Mathlib.GroupTheory.Nilpotent

/-!
# The solvable PSU₃(2) endpoint

Huppert II.10.12 gives order 72 for the actual projective matrix image
over the field of order four. A Sylow 3-subgroup has order nine. Its
normalizer is an extension of a 3-group by a 2-group, hence solvable;
Sylow counting bounds the normalizer's index by four. The coset action
then makes the full group solvable. This treats its actual structure,
without classifying it as a simple unitary carrier or using CFSG.

Basis change retains the stored Frobenius involution and covers arbitrary
Hermitian forms. Consequently all simple sections of this exceptional
endpoint are prime cyclic, as required for the unitary subfield induction.
Sources: Huppert II.10.12; GLS3, Theorem 6.5.3(d,g).
-/

namespace CFSG.Quasithin.MainConverse.UnitaryThreeSections

open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source.Unitary
open CFSG.KnownSimple

private theorem solvable_of_card_seventyTwo {G : Type*} [Group G]
    (hcard : Nat.card G = 72) : Group.IsSolvable G := by
  let : Finite G := Nat.finite_of_card_ne_zero (by omega)
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let P : Sylow 3 G := Classical.choice inferInstance
  have hP : Nat.card P = 9 := by
    rw [P.card_eq_multiplicity, hcard]
    rw [show 72 = 2 ^ 3 * 3 ^ 2 from rfl,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow,
      Nat.factorization_pow, Nat.prime_two.factorization, Nat.prime_three.factorization]
    norm_num
  have hi : (P : Subgroup G).index = 8 := by
    have h := (P : Subgroup G).card_mul_index
    rw [hP, hcard] at h
    omega
  have hcount : Nat.card (Sylow 3 G) ≤ 4 := by
    have hd := P.card_dvd_index
    rw [hi] at hd
    have hb := Nat.le_of_dvd (by decide : 0 < 8) hd
    have hm := card_sylow_modEq_one 3 G
    change Nat.card (Sylow 3 G) % 3 = 1 % 3 at hm
    interval_cases h : Nat.card (Sylow 3 G) <;> norm_num [h] at *
  let N := Subgroup.normalizer ((P : Subgroup G) : Set G)
  let P' := (P : Subgroup G).subgroupOf N
  let eP := Subgroup.subgroupOfEquivOfLe (P : Subgroup G).le_normalizer
  have hP' : IsPGroup 3 P' := P.isPGroup'.of_injective eP.toMonoidHom eP.injective
  let : Group.IsNilpotent P' := hP'.isNilpotent
  have hquot : Nat.card (N ⧸ P') ∣ 2 ^ 3 := by
    change (P : Subgroup G).relIndex N ∣ 8
    rw [← hi]
    exact (P : Subgroup G).relIndex_dvd_index_of_le (P : Subgroup G).le_normalizer
  let : Group.IsNilpotent (N ⧸ P') := (IsPGroup.of_card_dvd_pow hquot).isNilpotent
  let : Group.IsSolvable N := (Group.isSolvable_iff_subgroup_quotient P').2
    ⟨inferInstance, inferInstance⟩
  exact N.isSolvable_of_index_le_four (P.card_eq_index_normalizer ▸ hcount)

/-- The exceptional fixed-field order-two unitary model is solvable. -/
public theorem psu3_two_isSolvable {G : Type*} [Group G]
    (hG : ClassicalGroup.IsPSU G 3 2) : Group.IsSolvable G := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hG
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J 1 (by decide)
    (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hconj)
  let e' := e.trans (FormTransport.projectiveEquiv J C hC)
  obtain ⟨_hpoints, _rho, _a, _hinj, _hnatural, _hB, _hroots, _htwo, hc, _hthree⟩ :=
    BenderSuzuki.External.huppert_II_10_12 (FormTransport.standardForm J) 2 hcard
      (fixed_card J 1 (by decide) (by simpa only [pow_one] using hcard)
        (by simpa only [pow_one] using hconj)) rfl
  have h72 : Nat.card G = 72 := by
    rw [Nat.card_congr e'.toEquiv, hc]
    norm_num
  exact solvable_of_card_seventyTwo h72

/-- Includes simple sections of the whole PSU₃(2) model. -/
public theorem psu3_two_isKGroup_constructed {G : Type*} [Group G]
    (hG : ClassicalGroup.IsPSU G 3 2) : IsKGroup IsConstructedCarrier G := by
  let := psu3_two_isSolvable hG
  exact solvable_isKGroup_constructed G

end CFSG.Quasithin.MainConverse.UnitaryThreeSections
