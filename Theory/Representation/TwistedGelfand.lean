module

public import Theory.Representation.CharacterAverage
public import Theory.Representation.CommutingCompressions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic

/-!
# Finite-group twisted Gelfand weight multiplicity

For a finite additive parameter group, the inverse-character average is the
projection onto the actual character-weight intersection. An anti-involution
fixing the parameter image transports inverse-character matrix coefficients to
themselves, so compressed representation operators commute. Jacobson density
then bounds the image of this projector by one in an irreducible complex
representation. The argument retains the given representation, additive
character, and eigenspace intersection; no injectivity or nontriviality
assumption on the characters is used.
-/

namespace Representation

variable {G A V : Type*} [Group G] [AddCommGroup A]
  [AddCommGroup V] [Module ℂ V]

private theorem sigma_inv (sigma : G → G)
    (hmul : ∀ left right, sigma (left * right) = sigma right * sigma left)
    (element : G) : sigma (element⁻¹) = (sigma element)⁻¹ := by
  have hone : sigma 1 = 1 := by
    have heq : sigma 1 * 1 = sigma 1 * sigma 1 := by simpa using hmul 1 1
    exact (mul_left_cancel heq).symm
  apply eq_inv_of_mul_eq_one_left
  rw [← hmul, mul_inv_cancel, hone]

private theorem compressed_sigma_eq
    (rho : Representation ℂ G V) (u : AddChar A G) (psi : AddChar A ℂ)
    (sigma : G → G)
    (hmul : ∀ left right, sigma (left * right) = sigma right * sigma left)
    (hinvariant : ∀ function : G → ℂ,
      (∀ (left right : A) (element : G),
        function (u left * element * u right) =
          (psi left)⁻¹ * function element * (psi right)⁻¹) →
      ∀ element, function (sigma element) = function element)
    (proj : Module.End ℂ V)
    (hleft : ∀ parameter, rho (u parameter) * proj = psi parameter • proj)
    (hright : ∀ parameter, proj * rho (u parameter) = psi parameter • proj)
    (element : G) : proj * rho (sigma element) * proj = proj * rho element * proj := by
  have hcov (left right : A) (element : G) :
      proj * rho ((u left * element * u right)⁻¹) * proj =
        ((psi left)⁻¹ * (psi right)⁻¹) • (proj * rho (element⁻¹) * proj) := by
    simp only [mul_inv_rev, map_mul]
    rw [← u.map_neg_eq_inv right, ← u.map_neg_eq_inv left]
    calc
      proj * (rho (u (-right)) * (rho element⁻¹ * rho (u (-left)))) * proj =
          (proj * rho (u (-right))) * rho element⁻¹ * (rho (u (-left)) * proj) := by
            simp only [mul_assoc]
      _ = ((psi left)⁻¹ * (psi right)⁻¹) • (proj * rho element⁻¹ * proj) := by
        rw [hright, hleft, psi.map_neg_eq_inv, psi.map_neg_eq_inv]
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  ext vector
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro functional
  let coefficient : G → ℂ := fun element =>
    functional ((proj * rho element⁻¹ * proj) vector)
  have hcoeff := hinvariant coefficient (by
    intro left right element
    dsimp only [coefficient]
    rw [hcov]
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    ring) (element⁻¹)
  simpa only [coefficient, sigma_inv sigma hmul, inv_inv, map_sub, sub_eq_zero]
    using hcoeff

private theorem compressed_mul_comm_of_twisted_gelfand [Fintype A]
    (rho : Representation ℂ G V) (u : AddChar A G) (psi : AddChar A ℂ)
    (sigma : G → G)
    (hmul : ∀ left right, sigma (left * right) = sigma right * sigma left)
    (hfix : ∀ parameter, sigma (u parameter) = u parameter)
    (hinvariant : ∀ function : G → ℂ,
      (∀ (left right : A) (element : G),
        function (u left * element * u right) =
          (psi left)⁻¹ * function element * (psi right)⁻¹) →
      ∀ element, function (sigma element) = function element)
    (proj : Module.End ℂ V)
    (hsum : proj = (Fintype.card A : ℂ)⁻¹ • ∑ parameter : A,
      (psi parameter)⁻¹ • rho (u parameter))
    (hleft : ∀ parameter, rho (u parameter) * proj = psi parameter • proj)
    (hright : ∀ parameter, proj * rho (u parameter) = psi parameter • proj)
    (hidempotent : proj * proj = proj)
    (left right : G) :
    (proj * rho left * proj) * (proj * rho right * proj) =
      (proj * rho right * proj) * (proj * rho left * proj) := by
  have hsym := compressed_sigma_eq rho u psi sigma hmul hinvariant proj hleft hright
  have hexpand (left right : G) :
      proj * rho left * proj * rho right * proj =
        (Fintype.card A : ℂ)⁻¹ • ∑ parameter : A,
          (psi parameter)⁻¹ • (proj * rho (left * u parameter * right) * proj) := by
    conv_lhs => arg 1; arg 1; arg 2; rw [hsum]
    simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul,
      map_mul, mul_assoc]
  have hrev (left right : G) :
      proj * rho left * proj * rho right * proj =
        proj * rho (sigma right) * proj * rho (sigma left) * proj := by
    rw [hexpand, hexpand]
    congr 1
    apply Finset.sum_congr rfl
    intro parameter _
    congr 1
    rw [← hsym (left * u parameter * right), hmul, hmul, hfix]
    simp only [mul_assoc]
  have hproduct (left right : G) :
      (proj * rho left * proj) * (proj * rho right * proj) =
        proj * rho left * proj * rho right * proj := by
    calc
      _ = proj * rho left * (proj * proj) * rho right * proj := by
        simp only [mul_assoc]
      _ = _ := by rw [hidempotent]
  rw [hproduct, hrev, ← hproduct, hsym, hsym]

public theorem weight_finrank_le_one_of_twisted_gelfand
    [Finite G] [Finite A] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (hirred : Representation.IsIrreducible rho)
    (u : AddChar A G) (psi : AddChar A ℂ) (sigma : G → G)
    (_hinvolutive : Function.Involutive sigma)
    (hmul : ∀ left right, sigma (left * right) = sigma right * sigma left)
    (hfix : ∀ parameter, sigma (u parameter) = u parameter)
    (hinvariant : ∀ function : G → ℂ,
      (∀ (left right : A) (element : G),
        function (u left * element * u right) =
          (psi left)⁻¹ * function element * (psi right)⁻¹) →
      ∀ element, function (sigma element) = function element) :
    Module.finrank ℂ
      (⨅ parameter : A, Module.End.eigenspace (rho (u parameter)) (psi parameter) :
        Submodule ℂ V) ≤ 1 := by
  let _ := Fintype.ofFinite A
  let proj : Module.End ℂ V := characterAverage rho u psi
  have hspec := characterAverage_spec rho u psi
  have hcomm := compressed_mul_comm_of_twisted_gelfand rho u psi sigma hmul hfix
    hinvariant proj rfl hspec.2.1 hspec.2.2 hspec.1.isIdempotentElem
  rw [← hspec.1.range]
  exact finrank_range_le_one_of_commuting_compressions rho hirred proj
    hspec.1.isIdempotentElem hcomm

end Representation
