module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.Contracts
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder

/-!
# Concrete group comparisons for the M₂₂ representation sieve

Group orders separate M₂₂ from the special linear, symplectic and octonion
models in B.4.2. Its trivial center excludes the triple covers. For SU₃(2ⁿ),
the concrete root group forces 2³ⁿ to divide |M₂₂|, leaving n = 2; the
projective order then gives a contradiction. These comparisons require no
new simplicity or representation classification for the listed models.

Source: Aschbacher–Smith, B.4.2 and Table B.4.5, printed pp.86–87,
used in 13.8.21(2), p.956 (1 March 2004 manuscript).
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open BenderSuzuki.MatrixGroups Sporadic.Mathieu
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.ModelSieve

private theorem sl_card_mul (F : Type*) [Field F] [Finite F] (n : ℕ) [NeZero n] :
    Nat.card SL(n,F) * (Nat.card F - 1) =
      ∏ i : Fin n, (Nat.card F ^ n - Nat.card F ^ (i : ℕ)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(n,F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Atlas.ExceptionalSupport.card_psl_mul n

private theorem sl_three_card (F : Type*) [Field F] [Finite F] :
    Nat.card SL(3,F) = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h := sl_card_mul F 3
  change Nat.card SL(3,F) * (q-1) = _ at h
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one] at h
  have h1 : q^3-q = q*(q^2-1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h2 : q^3-q^2 = q^2*(q-1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q-1 by omega)
  rw [h, h1, h2]
  ring

private theorem sl_two_order_ne (q : ℕ) : q * (q^2-1) ≠ 443520 := by
  intro h
  by_cases hq : q ≤ 76
  · have hh : q * (q^2-1) ≤ 76 * (76^2-1) := by gcongr
    omega
  · have hh : 77 * (77^2-1) ≤ q * (q^2-1) := by gcongr <;> omega
    omega

private theorem sl_three_order_ne (q : ℕ) : q^3 * (q^3-1) * (q^2-1) ≠ 443520 := by
  intro h
  by_cases hq : q ≤ 5
  · interval_cases q <;> norm_num at h
  · have hh : 6^3 * (6^3-1) * (6^2-1) ≤ q^3 * (q^3-1) * (q^2-1) := by
      gcongr <;> omega
    omega

private theorem sp_order_ne (q : ℕ) : q^4 * (q^2-1) * (q^4-1) ≠ 443520 := by
  intro h
  by_cases hq : q ≤ 3
  · interval_cases q <;> norm_num at h
  · have hh : 4^4 * (4^2-1) * (4^4-1) ≤ q^4 * (q^2-1) * (q^4-1) := by
      gcongr <;> omega
    omega

private theorem g2_order_ne (q : ℕ) : q^6 * (q^6-1) * (q^2-1) ≠ 443520 := by
  intro h
  by_cases hq : q ≤ 2
  · interval_cases q <;> norm_num at h
  · have hh : 3^6 * (3^6-1) * (3^2-1) ≤ q^6 * (q^6-1) * (q^2-1) := by
      gcongr <;> omega
    omega

variable {L : Type*} [Group L] (e : L ≃* M22)
include e

/-- The checked native order transports through the actual marking. -/
theorem card_of_equiv_m22 : Nat.card L = 443520 :=
  (Nat.card_congr e.toEquiv).trans m22_order

/-- M₂₂ cannot be a triple cover: its actual center is trivial. -/
theorem not_center_three (c : center L ≃* Multiplicative (ZMod 3)) : False := by
  have h1 : Nat.card (center L) = 1 := by
    rw [Nat.card_congr (centerCongr e).toEquiv, m22_center_eq_bot]
    simp
  have h3 : Nat.card (center L) = 3 :=
    (Nat.card_congr c.toEquiv).trans (Nat.card_zmod 3)
  omega

/-- No finite special-linear group of degree two has the order of M₂₂. -/
theorem not_linear_two (F : Type*) [Field F] [Finite F]
    (f : L ≃* SL(2,F)) : False := by
  have h := (Nat.card_congr f.toEquiv).symm.trans (card_of_equiv_m22 e)
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup] at h
  exact sl_two_order_ne _ h

/-- The characteristic-two projective degree-two group equals its special model. -/
theorem not_projective_two (F : Type*) [Field F] [Finite F] [CharP F 2]
    (f : L ≃* PSL(2,F)) : False := by
  have hc := BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (K := F) (by simpa using (CharTwo.neg_eq (1 : F)))
  have h := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [hc, mul_one, ← Nat.card_congr f.toEquiv, card_of_equiv_m22 e] at h
  exact sl_two_order_ne _ h.symm

/-- No finite special-linear group of degree three has the order of M₂₂. -/
theorem not_linear_three (F : Type*) [Field F] [Finite F]
    (f : L ≃* SL(3,F)) : False := by
  have h := (Nat.card_congr f.toEquiv).symm.trans (card_of_equiv_m22 e)
  rw [sl_three_card] at h
  exact sl_three_order_ne _ h

/-- No finite symplectic four-space group has the order of M₂₂. -/
theorem not_symplectic_four (F : Type*) [Field F] [Finite F]
    (f : L ≃* Matrix.symplecticGroup (Fin 2) F) : False := by
  have h := (Nat.card_congr f.toEquiv).symm.trans (card_of_equiv_m22 e)
  rw [Theory.SpecificGroups.SymplecticFour.card_sp] at h
  exact sp_order_ne _ h

/-- No finite full octonion group has the order of M₂₂. -/
theorem not_g2 (F : Type*) [Field F] [Finite F]
    (f : L ≃* Atlas.G2.Model F) : False := by
  have h := (Nat.card_congr f.toEquiv).symm.trans (card_of_equiv_m22 e)
  rw [Atlas.G2.card_Model] at h
  exact g2_order_ne _ h

/-- The derived binary octonion group has order 6048. -/
theorem not_g2_derived_two (f : L ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have h := (Nat.card_congr f.toEquiv).symm.trans (card_of_equiv_m22 e)
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
    Atlas.G2.BinaryException.card_H] at h
  norm_num at h

/-- Both small alternating actors in the full FF list are excluded by their orders. -/
theorem not_small_alternating (n : ℕ) (hn : n = 6 ∨ n = 7)
    (f : L ≃* alternatingGroup (Fin n)) : False := by
  have h := (Nat.card_congr f.toEquiv).symm.trans (card_of_equiv_m22 e)
  rcases hn with rfl | rfl
  all_goals
    rw [nat_card_alternatingGroup] at h
    norm_num at h

/-- The two higher binary linear actors in B.4.2 have different orders. -/
theorem not_binary_linear (n : ℕ) (hn : n = 4 ∨ n = 5)
    (f : L ≃* SL(n,ZMod 2)) : False := by
  have h := (Nat.card_congr f.toEquiv).symm.trans (card_of_equiv_m22 e)
  rcases hn with rfl | rfl
  · have hc := sl_card_mul (ZMod 2) 4
    rw [h] at hc
    norm_num [Fin.prod_univ_succ] at hc
  · have hc := sl_card_mul (ZMod 2) 5
    rw [h] at hc
    norm_num [Fin.prod_univ_succ] at hc

/-- The ternary unitary rows use SU over the quadratic matrix field.
Its projective quotient already gives the required order obstruction. -/
theorem not_unitary_three (F : BinaryField) (n : ℕ) (hn : 2 ≤ n)
    (degree : F.degree = 2 * n) (J : HermitianForm 3 F.Carrier)
    (conjugation : ∀ x, J.conj x = x ^ (2 ^ n))
    (f : L ≃* J.specialSubgroup) : False := by
  have hF : Nat.card F.Carrier = (2 ^ n) ^ 2 := by
    rw [F.card_eq, degree, Nat.mul_comm 2 n, pow_mul]
  have hd : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) ∣ 443520 := by
    rw [← card_of_equiv_m22 e, Nat.card_congr f.toEquiv]
    exact J.specialSubgroup.card_map_dvd Matrix.ProjGenLinGroup.mk
  have hc : (2 ^ n) ^ 3 ∣ 443520 :=
    (HermitianForm.BinarySylowOrder.cube_dvd_card_projective J (by omega) hF conjugation).trans hd
  have hn3 : n < 3 := by
    by_contra h
    have hp : 2 ^ 9 ∣ (2 ^ n) ^ 3 := by
      rw [← pow_mul]
      exact Nat.pow_dvd_pow 2 (by omega)
    exact (by norm_num : ¬ 2 ^ 9 ∣ 443520) (hp.trans hc)
  have hn2 : n = 2 := by omega
  subst n
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2
    (by decide) hF conjugation
  rw [Representation.SU3.BinaryDegree.card_projective J hF hfixed] at hd
  norm_num at hd

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.ModelSieve
