module
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootCoordinates
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Inner
public import Mathlib.Algebra.CharP.CharAndCard
/-!
# Defining-characteristic roots inverted by odd PSL₃ involutions

The standard involution diag(-1,-1,1) inverts x₀₂(1), whose order is the
prime-field characteristic. Lift an arbitrary projective involution to SL₃
and use its determinant-one eigenbasis to transport this root. This retains
the actual projective element and the original field parameter.

Source: Aschbacher–Smith E.2.17, printed p.230.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.OddInvolutionFixed Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace Matrix.PSL3.OddInvolutionRoot
variable {F : Type*} [Field F] [Finite F]
private theorem root_order {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    orderOf (rootElement (show (0 : Fin 3) ≠ 2 by decide) (1:F)) = p := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by simpa only [← Nat.card_eq_fintype_card] using hF)
  apply orderOf_eq_prime
  · rw [← rootElement_natCast, CharP.cast_eq_zero, rootElement_zero]
  · exact (rootElement_eq_one_iff _ _).not.mpr one_ne_zero

omit [Finite F] in
private theorem standard_inverts : SL3.standardInvolution F *
    SpecialLinearGroup.transvection (show (0:Fin 3)≠2 by decide) (1:F) *
    (SL3.standardInvolution F)⁻¹ =
    (SpecialLinearGroup.transvection (show (0:Fin 3)≠2 by decide) (1:F))⁻¹ := by
  have hi : (SL3.standardInvolution F)⁻¹ = SL3.standardInvolution F :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using SL3.standardInvolution_sq F)
  rw [hi, SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (SL3.standardInvolution F).val * (SpecialLinearGroup.transvection (show (0:Fin 3)≠2 by decide) (1:F)).val * (SL3.standardInvolution F).val = (SpecialLinearGroup.transvection (show (0:Fin 3)≠2 by decide) (-1:F)).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SL3.standardInvolution, SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]
theorem exists_inverted_root {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (t : PSL(3,F)) (ht : orderOf t = 2) :
    ∃ r : PSL(3,F), orderOf r = p ∧ t * r * t⁻¹ = r⁻¹ := by
  have h2 : (2:F)≠0 := by
    let := Fintype.ofFinite F
    intro hz
    have hc : ringChar F = 2 := CharP.ringChar_of_prime_eq_zero Nat.prime_two hz
    have he := FiniteField.even_card_iff_char_two.mp hc
    rw [← Nat.card_eq_fintype_card, hF] at he
    have := Nat.odd_iff.mp ho
    omega
  obtain ⟨x, hx, rfl⟩ := involution_lift t ht
  obtain ⟨s, hs⟩ := SL3.exists_standardInvolution_conjugator F x hx
    h2
  let e := MulAut.conj (projection F s)
  let r := rootElement (show (0:Fin 3)≠2 by decide) (1:F)
  have htx : e (projection F (SL3.standardInvolution F)) = projection F x := by
    simpa only [e, MulAut.conj_apply, map_mul, map_inv] using congrArg (projection F) hs
  refine ⟨e r, (e.orderOf_eq r).trans (root_order hp hF), ?_⟩
  calc
    projection F x * e r * (projection F x)⁻¹ =
        e (projection F (SL3.standardInvolution F) * r * (projection F (SL3.standardInvolution F))⁻¹) := by
      rw [map_mul,map_mul,map_inv,htx]
    _ = e r⁻¹ := by
      apply congrArg e
      exact congrArg (projection F) (standard_inverts (F:=F))
    _ = (e r)⁻¹ := map_inv e r
end Matrix.PSL3.OddInvolutionRoot
