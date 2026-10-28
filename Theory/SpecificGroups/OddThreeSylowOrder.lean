module

public import Theory.SpecificGroups.SL3.SplitMonomial.SolvableNormal
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import BenderSuzuki.External.Huppert.II.theorem_10_12

/-!
# Sixteen divides the orders of odd degree-three classical groups

The determinant-corrected GL₂ embedding supplies the linear assertion.
The central kernel of SL₃ → PSL₃ is odd, so the same two-part survives
projectivization. For PSU₃ the unitary order formula has an even factor
`q³ + 1` and a factor `q² - 1` divisible by eight; its scalar divisor is
odd. The special unitary assertion follows from its surjection onto PSU₃.

These are the order comparisons needed for the containing-model inspection
in Aschbacher–Smith, C.5.13, printed pp.162–163.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Theory.SpecificGroups.OddThreeSylowOrder

/-- The full linear group in determinant-one degree three has two-part
at least sixteen over every odd finite field. -/
theorem special_sixteen_dvd_card {F : Type*} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) : 16 ∣ Nat.card (SL(3,F)) := by
  let T : Sylow 2 (SL(3,F)) := Classical.choice inferInstance
  have hd : Nat.card (T : Subgroup (SL(3,F))) ∣ Nat.card (SL(3,F)) :=
    card_subgroup_dvd_card (T : Subgroup (SL(3,F)))
  exact Nat.dvd_trans (Matrix.SL3.SplitMonomial.sixteen_dvd_card_sylow (F := F) hF T) hd

/-- The odd scalar center cannot remove any two-part on passage to PSL₃. -/
theorem projective_sixteen_dvd_card {F : Type*} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) : 16 ∣ Nat.card (PSL(3,F)) := by
  let f := Matrix.PSL3.projection F
  have he := f.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (Matrix.PSL3.projection_surjective F),
    Subgroup.card_top] at he
  have hk : Nat.Coprime 16 (Nat.card f.ker) := by
    change Nat.Coprime (2^4) (Nat.card (Matrix.PSL3.projection F).ker)
    rw [Matrix.PSL3.projection_ker]
    exact (Matrix.SL3.odd_card_center F).coprime_two_left.pow_left 4
  apply hk.dvd_of_dvd_mul_left
  rw [he]
  exact special_sixteen_dvd_card hF

private theorem sixteen_dvd_unitary_order {q : ℕ} (ho : Odd q) :
    16 ∣ (q^3+1)*q^3*(q^2-1) / Nat.gcd 3 (q+1) := by
  have hmod : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by
    have := Nat.odd_iff.mp ho
    omega
  have hs : q^2 % 8 = 1 := by
    rw [Nat.pow_mod]
    rcases hmod with h | h | h | h <;> simp [h]
  have h8 : 8 ∣ q^2-1 := by omega
  have h2 : 2 ∣ q^3+1 := (ho.pow.add_odd odd_one).two_dvd
  have h16 : 16 ∣ (q^3+1)*q^3*(q^2-1) :=
    Nat.mul_dvd_mul (h2.trans (dvd_mul_right _ _)) h8
  have hg : Nat.gcd 3 (q+1) ∣ (q^3+1)*q^3*(q^2-1) := by
    have hd : q+1 ∣ q^3+1 := by
      simpa only [one_pow] using (show Odd 3 by decide).nat_add_dvd_pow_add_pow q 1
    exact ((Nat.gcd_dvd_right 3 (q+1)).trans hd).trans
      ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
  have hc : Nat.Coprime 16 (Nat.gcd 3 (q+1)) := by
    change Nat.Coprime (2^4) _
    exact (Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 (q+1))).coprime_two_left.pow_left 4
  apply hc.dvd_of_dvd_mul_right
  rwa [Nat.div_mul_cancel hg]

/-- The unitary order formula gives a two-part at least sixteen, with the
original field involution retained by the standard-form equivalence. -/
theorem unitary_projective_sixteen_dvd_card
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p^2)
    (hconj : ∀ x, J.conj x = x^p) :
    16 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa using hcard) (by simpa using hconj)
  obtain ⟨e⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J p hcard hfixed
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ :=
    BenderSuzuki.External.huppert_II_10_12
      (HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J)
      p hcard hfixed rfl
  rw [Nat.card_congr e.toEquiv, hc]
  exact sixteen_dvd_unitary_order ho

/-- The special unitary group surjects onto the projective unitary group. -/
theorem unitary_special_sixteen_dvd_card
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p^2)
    (hconj : ∀ x, J.conj x = x^p) :
    16 ∣ Nat.card J.specialSubgroup :=
  (unitary_projective_sixteen_dvd_card J hp ho hcard hconj).trans
    (card_dvd_of_surjective J.specialToProjective J.specialToProjective_surjective)

end Theory.SpecificGroups.OddThreeSylowOrder
