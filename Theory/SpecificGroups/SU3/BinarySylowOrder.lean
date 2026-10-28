module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Mathlib.GroupTheory.Sylow

/-!
# The defining two-part of projective unitary groups in dimension three

An actual Hermitian basis change preserves the stored quadratic Frobenius and
identifies the full projective group with the antidiagonal model. Its explicit
upper root subgroup has order q³. Sylow divisibility transfers this lower bound
to every Sylow two-subgroup, for q = 2ⁿ. The coefficient field has order q².

Source: Huppert II.10.12 and Aschbacher–Smith, the proof of 16.3.4,
printed p.1178. No simplicity or ambient embedding premise is needed.
-/

namespace BenderSuzuki.MatrixGroups.HermitianForm.BinarySylowOrder
open Subgroup OddPrimeSylow.NormalizedOuter

/-- The explicit root group supplies the defining-characteristic cube in PSU₃. -/
public theorem cube_dvd_card_projective {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : n ≠ 0) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    (2 ^ n) ^ 3 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hf : Nat.card {x : F // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (Nat.pos_of_ne_zero hn) hF hconj
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J (2 ^ n) hF hf
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨_, _, _, _, _, _, hroot, _⟩ :=
    BenderSuzuki.External.huppert_II_10_12 (FormTransport.standardForm J) (2 ^ n) hF hf rfl
  obtain ⟨R, _, _, _, _, _, _, _, hR, _⟩ := hroot
  rw [← hR]
  exact card_subgroup_dvd_card _

/-- Every actual Sylow two-subgroup of PSU₃(2ⁿ) has order at least `2³ⁿ`. -/
public theorem cube_le_sylow_card {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : n ≠ 0) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    (2 ^ n) ^ 3 ≤ Nat.card S := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  apply Nat.le_of_dvd Nat.card_pos
  rw [← pow_mul]
  exact S.pow_dvd_card_of_pow_dvd_card (by simpa [pow_mul] using cube_dvd_card_projective J hn hF hconj)

end BenderSuzuki.MatrixGroups.HermitianForm.BinarySylowOrder
