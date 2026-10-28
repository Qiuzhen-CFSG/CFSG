module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

/-!
# Prime support of two-dimensional multiplicity groups

Every prime in GL₂(F) occurs in SL₂(F), by their literal order formulas.
Thus a faithful two-dimensional multiplicity action whose order is coprime
to every odd component prime is a two-group. The field is arbitrary here;
the source application uses a binary field and the actual orbit index.
Source: Aschbacher--Smith, D.3.21, printed p.206.
-/

public section
namespace Theory.LinearAlgebra.BinaryMultiplicity
open scoped MatrixGroups

/-- Every prime divisor of GL₂(F) already divides SL₂(F). -/
theorem prime_dvd_specialLinear_of_dvd_linearAut
    {F : Type*} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card ((Module.End F (Fin 2 → F))ˣ)) :
    p ∣ Nat.card (SL(2,F)) := by
  classical
  let := Fintype.ofFinite F
  let e := Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := F)
  rw [← Nat.card_congr e.toEquiv,Matrix.card_GL_field] at hd
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup]
  simp only [Fin.prod_univ_two,Fin.val_zero,Fin.val_one,pow_zero,pow_one,
    ← Nat.card_eq_fintype_card] at hd
  let q := Nat.card F
  have hq : 1 ≤ q := Nat.card_pos
  have he : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_left_distrib]
    simp [pow_two]
  rcases hp.dvd_mul.mp hd with h | h
  · exact dvd_mul_of_dvd_right h _
  · change p ∣ q ^ 2 - q at h
    rw [he] at h
    rcases hp.dvd_mul.mp h with h | h
    · exact dvd_mul_of_dvd_left h _
    · have hq2 : q ^ 2 - 1 = (q-1)*(q+1) := by
        have hh := Nat.sub_add_cancel hq
        have hh2 := Nat.sub_add_cancel (show 1 ≤ q ^ 2 by nlinarith)
        nlinarith
      change p ∣ q * (q ^ 2 - 1)
      rw [hq2]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h _) _

/-- The odd-prime exclusion for the component kills every odd multiplicity prime. -/
theorem isPGroup_two_of_linearAut_embedding
    {F C : Type*} [Field F] [Finite F] [Group C] [Finite C]
    (f : C →* (Module.End F (Fin 2 → F))ˣ) (hf : Function.Injective f)
    (hcop : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card (SL(2,F)) →
      Nat.Coprime p (Nat.card C)) : IsPGroup 2 C := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  have hprime := (Nat.mem_primeFactors.mp hp).1
  have hd := (Nat.mem_primeFactors.mp hp).2.1
  have he : p = 2 := by
    by_contra hn
    have hL := prime_dvd_specialLinear_of_dvd_linearAut hprime
      (hd.trans (Subgroup.card_dvd_of_injective f hf))
    exact hprime.coprime_iff_not_dvd.mp (hcop p hprime hn hL) hd
  simp [he,Nat.prime_two]
end Theory.LinearAlgebra.BinaryMultiplicity
