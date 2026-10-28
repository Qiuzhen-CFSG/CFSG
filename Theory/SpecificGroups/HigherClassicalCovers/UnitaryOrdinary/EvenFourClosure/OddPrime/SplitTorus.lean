module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.Reduction
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus.Coefficients
public import Theory.GroupTheory.PerfectCentralCoverThreeCycleNorm

/-!
# The binary split torus and its central-cover application

The actual reciprocal diagonal torus on two hyperbolic pairs uses roots
of unity of order p^v_p(q−1), retaining all higher prime powers. Its
projective image has the square of that order. The ambient pair swap
forces arbitrary lifts of the two generators to commute. Basis transport
identifies this matrix model with the original antidiagonal SU₄ group.

The covering exclusion is conditional only on the explicit ambient
primary-order bound. That bound is not proved here: a GL₄(q²) order
comparison has excessive p-torsion when p divides q−1. The torus geometry
adapts the checked `UnitaryQuadratic.PairedTorus` construction.
Source: Aschbacher–Smith I.1.1–4, printed pp.407–408 of
`refs/quasithin.pdf`, and GLS3 §6.1.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups PerfectCentralCovering
open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus

@[expose] public noncomputable section

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime

variable {F : Type*} [Field F] [Finite F]

/-- The literal reciprocal torus with all p-primary roots of unity from the fixed field. -/
def splitProjective (J : HermitianForm 4 F) (n p : ℕ)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    (Fin 2 → rootsOfUnity (primaryExponent (2 ^ n) p) F) →*
      ProjectiveSpecialUnitaryMatrixGroup (OddFourRanks.Defining.hyperbolicForm J) :=
  projective J _ (roots_fixed J (Nat.one_le_pow n 2 (by decide)) hconj
    (primaryExponent_dvd (2 ^ n) p))

/-- The coefficient subgroup retains every p-power in q−1. -/
theorem card_split_coefficients (n : ℕ) {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card F = (2 ^ n) ^ 2) :
    Nat.card (rootsOfUnity (primaryExponent (2 ^ n) p) F) = primaryExponent (2 ^ n) p := by
  let : NeZero (primaryExponent (2 ^ n) p) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  apply FiniteField.card_rootsOfUnity_of_dvd
  rw [hcard]
  apply (primaryExponent_dvd (2 ^ n) p).trans
  have he : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    simpa only [one_pow] using Nat.sq_sub_sq (2 ^ n) 1
  rw [he]
  exact dvd_mul_left _ _

/-- Faithful projectivization gives the full rank-two primary torus order. -/
theorem card_splitProjective_range (J : HermitianForm 4 F) (n : ℕ)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    Nat.card (splitProjective J n p hconj).range = primaryExponent (2 ^ n) p ^ 2 := by
  have hc := card_split_coefficients (p := p) n hcard
  simpa only [splitProjective, hc] using card_range J _
    (roots_fixed J (Nat.one_le_pow n 2 (by decide)) hconj (primaryExponent_dvd (2 ^ n) p))
    (by rw [hc]; exact primaryExponent_odd (2 ^ n) hp)

theorem not_dvd_kernel_of_split_card_bound
    (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hb : ¬ p * primaryExponent (2 ^ n) p ^ 2 ∣ Nat.card (Standard J))
    {E : Type*} [Group E] [Finite E] (d : Cover E (Standard J)) :
    ¬ p ∣ Nat.card d.toMonoidHom.ker := by
  let H := OddFourRanks.Defining.hyperbolicForm J
  obtain ⟨e₀⟩ := UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
    H n hn hcard hconj
  let e : ProjectiveSpecialUnitaryMatrixGroup H ≃* Standard J := e₀
  have hi : ¬ p ∣ (splitProjective J n p hconj).range.index := by
    intro hd
    apply hb
    rw [← Nat.card_congr e.toEquiv,
      ← (splitProjective J n p hconj).range.card_mul_index,
      card_splitProjective_range J n hcard hconj hp]
    simpa only [Nat.mul_comm p] using Nat.mul_dvd_mul_left (primaryExponent (2 ^ n) p ^ 2) hd
  let C := rootsOfUnity (primaryExponent (2 ^ n) p) F
  have hC : ∀ u : C, J.conj (u.val : F) = (u.val : F) :=
    roots_fixed J (Nat.one_le_pow n 2 (by decide)) hconj (primaryExponent_dvd (2 ^ n) p)
  have ho : (Nat.card C).Coprime 2 := by
    rw [card_split_coefficients n hcard]
    exact primaryExponent_odd (2 ^ n) hp
  obtain ⟨x,y,s,hgen,hxy,hsx,hsy,hx⟩ := exists_pair J C hC
  let f : Cover E (ProjectiveSpecialUnitaryMatrixGroup H) := {
    toMonoidHom := e.symm.toMonoidHom.comp d.toMonoidHom
    surjective := e.symm.surjective.comp d.surjective
    isPerfect := d.isPerfect
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective]
      exact d.ker_le_center }
  have hf := f.not_dvd_kernel_of_swapped_pair_at_prime_index
    (projective J C hC).range x y s hgen hxy hsx hsy ho hx hi
  change ¬ p ∣ Nat.card (e.symm.toMonoidHom.comp d.toMonoidHom).ker at hf
  rwa [MonoidHom.ker_comp_of_injective _ _ e.symm.injective] at hf

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime
