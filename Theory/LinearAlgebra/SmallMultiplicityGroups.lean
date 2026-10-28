module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

/-!
# Small multiplicity groups over the binary and four-element fields

The standard general linear group order formula gives orders dividing 180
in dimensions at most two over either field. A finite group embedding in a
product of two such automorphism groups therefore has order dividing 180².
When its order is coprime to 3 and 5, it divides 16 and the group is a two-group.
The factors may have different fields and dimensions; dimension zero is allowed.

This is the multiplicity-centralizer arithmetic in the A₅ case of
Aschbacher--Smith D.3.21, printed p.206. The coordinate embedding and the
multiplicity bound are separate mathematical inputs.
-/

@[expose] public section
namespace Theory.LinearAlgebra.SmallMultiplicityGroups

/-- The order of the small multiplicity automorphism group divides 180. -/
theorem card_linearAut_dvd_180
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2 ∨ Nat.card F = 4)
    {k : ℕ} (hk : k ≤ 2) :
    Nat.card ((Fin k → F) ≃ₗ[F] (Fin k → F)) ∣ 180 := by
  classical
  let := Fintype.ofFinite F
  let e := (Matrix.GeneralLinearGroup.toLin (n := Fin k) (R := F)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin k → F))
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  have hq : Fintype.card F = 2 ∨ Fintype.card F = 4 := by
    simpa only [Nat.card_eq_fintype_card] using hF
  rcases hq with hq | hq <;> rw [hq] <;>
    interval_cases k <;> norm_num [Fin.prod_univ_succ]

/-- Only 2, 3 and 5 can divide the order of a small multiplicity group. -/
theorem prime_divisors_linearAut
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2 ∨ Nat.card F = 4)
    {k : ℕ} (hk : k ≤ 2) {p : ℕ} (hp : p.Prime)
    (hdiv : p ∣ Nat.card ((Fin k → F) ≃ₗ[F] (Fin k → F))) :
    p = 2 ∨ p = 3 ∨ p = 5 := by
  have hd := hdiv.trans (card_linearAut_dvd_180 hF hk)
  rw [show 180 = 2 ^ 2 * 3 ^ 2 * 5 by norm_num] at hd
  rcases hp.dvd_mul.mp hd with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · have he := (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp (hp.dvd_of_dvd_pow h)
      rcases he with he | he
      · exact (hp.ne_one he).elim
      · exact Or.inl he
    · have he := (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp (hp.dvd_of_dvd_pow h)
      rcases he with he | he
      · exact (hp.ne_one he).elim
      · exact Or.inr (Or.inl he)
  · have he := (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h
    rcases he with he | he
    · exact (hp.ne_one he).elim
    · exact Or.inr (Or.inr he)

/-- Coprimality removes the odd factors from an actual two-coordinate embedding. -/
theorem card_dvd_sixteen_of_injective_pair
    {F₁ F₂ C : Type*} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂]
    [Group C] [Finite C]
    (hF₁ : Nat.card F₁ = 2 ∨ Nat.card F₁ = 4)
    (hF₂ : Nat.card F₂ = 2 ∨ Nat.card F₂ = 4)
    {k₁ k₂ : ℕ} (hk₁ : k₁ ≤ 2) (hk₂ : k₂ ≤ 2)
    (f : C →* (((Fin k₁ → F₁) ≃ₗ[F₁] (Fin k₁ → F₁)) ×
      ((Fin k₂ → F₂) ≃ₗ[F₂] (Fin k₂ → F₂))))
    (hf : Function.Injective f)
    (hthree : Nat.Coprime 3 (Nat.card C)) (hfive : Nat.Coprime 5 (Nat.card C)) :
    Nat.card C ∣ 16 := by
  have hdiv := Subgroup.card_dvd_of_injective f hf
  rw [Nat.card_prod] at hdiv
  have hd : Nat.card C ∣ 180 * 180 := hdiv.trans
    (Nat.mul_dvd_mul (card_linearAut_dvd_180 hF₁ hk₁) (card_linearAut_dvd_180 hF₂ hk₂))
  have hcop : Nat.Coprime (Nat.card C) (3 ^ 4 * 5 ^ 2) :=
    (hthree.symm.pow_right 4).mul_right (hfive.symm.pow_right 2)
  apply hcop.dvd_of_dvd_mul_right
  convert hd using 1; norm_num

/-- A faithful pair of small multiplicity actions with order prime to 15 is a two-group. -/
theorem isPGroup_two_of_injective_pair
    {F₁ F₂ C : Type*} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂]
    [Group C] [Finite C]
    (hF₁ : Nat.card F₁ = 2 ∨ Nat.card F₁ = 4)
    (hF₂ : Nat.card F₂ = 2 ∨ Nat.card F₂ = 4)
    {k₁ k₂ : ℕ} (hk₁ : k₁ ≤ 2) (hk₂ : k₂ ≤ 2)
    (f : C →* (((Fin k₁ → F₁) ≃ₗ[F₁] (Fin k₁ → F₁)) ×
      ((Fin k₂ → F₂) ≃ₗ[F₂] (Fin k₂ → F₂))))
    (hf : Function.Injective f)
    (hthree : Nat.Coprime 3 (Nat.card C)) (hfive : Nat.Coprime 5 (Nat.card C)) :
    IsPGroup 2 C :=
  IsPGroup.of_card_dvd_pow (n := 4)
    (card_dvd_sixteen_of_injective_pair hF₁ hF₂ hk₁ hk₂ f hf hthree hfive)

/-- The same conclusion for the endomorphism-unit groups produced by commutants. -/
theorem isPGroup_two_of_injective_unit_pair
    {F₁ F₂ C : Type*} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂]
    [Group C] [Finite C]
    (hF₁ : Nat.card F₁ = 2 ∨ Nat.card F₁ = 4)
    (hF₂ : Nat.card F₂ = 2 ∨ Nat.card F₂ = 4)
    {k₁ k₂ : ℕ} (hk₁ : k₁ ≤ 2) (hk₂ : k₂ ≤ 2)
    (f : C →* ((Module.End F₁ (Fin k₁ → F₁))ˣ ×
      (Module.End F₂ (Fin k₂ → F₂))ˣ))
    (hf : Function.Injective f)
    (hthree : Nat.Coprime 3 (Nat.card C)) (hfive : Nat.Coprime 5 (Nat.card C)) :
    IsPGroup 2 C := by
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv F₁ (Fin k₁ → F₁)).prodCongr
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F₂ (Fin k₂ → F₂))
  exact isPGroup_two_of_injective_pair hF₁ hF₂ hk₁ hk₂
    (e.toMonoidHom.comp f) (e.injective.comp hf) hthree hfive

end Theory.LinearAlgebra.SmallMultiplicityGroups
