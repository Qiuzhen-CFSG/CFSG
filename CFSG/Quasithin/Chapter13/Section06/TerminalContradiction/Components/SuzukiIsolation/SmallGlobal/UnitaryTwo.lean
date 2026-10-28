module

public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SmallGlobal.UnitaryTwo.Counting
public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# The prime-divisor obstruction for the actual PSU₄(2) model

The catalogue permits an arbitrary field of order four and arbitrary
nondegenerate Hermitian form with square Frobenius. The existing
orthonormal-basis and coefficient transports identify its special unitary
group with the identity-form model over `GoldenFour`. The latter embeds
in the full isometry group of order 77760, which has no divisor seven.
The actual special-to-projective surjection preserves order divisibility.

Thus this calculation retains the catalogue's genuine model equivalence,
without recognizing the group from its order or assuming simplicity.
It discharges the unitary-four endpoint in the small-global sieve for
Aschbacher–Smith 5.2.3 and 13.6.27, printed pp.649 and 934
(PDF pp.666 and 951), `refs/quasithin.pdf`.
-/

open Matrix Atlas.Algebra

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SmallGlobalUnitary

private abbrev F := GoldenFour
private abbrev U (n : ℕ) := Matrix.unitaryGroup (Fin n) F

open BenderSuzuki.MatrixGroups

def form : HermitianForm 4 F where
  conj := starRingAut
  conj_involutive := fun x => star_star x
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

def specialToUnitary : form.specialSubgroup →* U 4 where
  toFun A := ⟨A.val.val, by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    have h := ((form.mem_specialSubgroup_iff A.val).mp A.property).1
    change star A.val.val * 1 * A.val.val = 1 at h
    simpa only [mul_one] using h⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem specialToUnitary_injective : Function.Injective specialToUnitary := by
  intro A B h
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val h

public theorem not_thirtyFive_dvd_of_unitary_two {G : Type*} [Group G]
    (hm : ClassicalGroup.IsPSU G 4 2) : ¬ 35 ∣ Nat.card G := by
  obtain ⟨E, _, _, J, hE, hconj, ⟨e⟩⟩ := hm
  have hJ : Nat.card {x : E // J.conj x = x} = 2 := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1 (by decide)
        (by simpa only [pow_one] using hE) (by simpa only [pow_one] using hconj)
  have hF : Nat.card F = 2 ^ 2 := by
    rw [Nat.card_eq_fintype_card, Atlas.Algebra.goldenFour_card]
    decide
  have hfixed : Nat.card {x : F // form.conj x = x} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  obtain ⟨es⟩ := HermitianForm.nonempty_specialEquiv_of_card J form 2 hE hJ hF hfixed
  intro hd
  rw [Nat.card_congr e.toEquiv] at hd
  have hs := hd.trans (J.specialSubgroup.card_map_dvd Matrix.ProjGenLinGroup.mk)
  rw [Nat.card_congr es.toEquiv] at hs
  have hu := hs.trans (Subgroup.card_dvd_of_injective specialToUnitary
    specialToUnitary_injective)
  rw [card_unitary_four] at hu
  norm_num at hu

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SmallGlobalUnitary
