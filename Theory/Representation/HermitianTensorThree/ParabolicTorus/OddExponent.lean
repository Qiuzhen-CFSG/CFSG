module

public import Theory.Representation.HermitianTensorThree.ParabolicTorus.OddExponent.LinearReduction

/-!
# Reduction of the odd Hermitian parabolic exponent to natural matrices

An odd fixed-field linear element of the actual binary normalizer has a
GL₃ congruence lift of odd order. If it normalizes a conjugate of either
marked image parabolic, conjugating the lift by the same SL₃ element makes
it normalize the standard image parabolic. Its order in the binary action
is unchanged.

The remaining inputs recover the corresponding natural point or plane
and bound the order of its one- and two-dimensional blocks, including the
nonsplit case. Supplying those two matrix calculations proves the original
`OddLinearParabolicExponent` contract with no coefficient, central-kernel,
or conjugacy premises left over. This module does not yet prove the two
matrix calculations.

The contract is consumed by `LinearThreeTorus.Setup.not_intermediate_of_geometry`
in Chapter 8. The fixed-space linearity calculation is independent of this
reduction and remains an input of that Chapter 8 consumer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.4.2 setup,
printed p.380, and Proposition 8.2.3, printed pp.715–716.
-/

public section
noncomputable section
namespace Representation.HermitianTensorThree.ParabolicTorus
open ImageOuter OddExponent
variable (n : ℕ) [NeZero n]

private theorem mem_normalizer_of_conjugate {G : Type*} [Group G] (P : Subgroup G) (u e : G)
    (he : e ∈ Subgroup.normalizer
      (P.map (MulAut.conj u).toMonoidHom : Set G)) :
    u⁻¹ * e * u ∈ Subgroup.normalizer (P : Set G) := by
  rw [← Subgroup.map_equiv_normalizer_eq] at he
  obtain ⟨b, hb, hbe⟩ := he
  change u * b * u⁻¹ = e at hbe
  have h : u⁻¹ * e * u = b := by rw [← hbe]; group
  rwa [h]

/-- The original exponent contract follows from the two natural matrix
calculations. Both image-parabolic types and every cover conjugate are included. -/
theorem oddLinearParabolicExponent_of_matrix_inputs
    (hgeometry : CongruenceParabolicRecovery n)
    (hexponent : NaturalParabolicOddExponent n) : OddLinearParabolicExponent n := by
  intro e heN ho heF heP
  obtain ⟨g, hg⟩ := mem_congruenceImage_of_odd_of_isFixedFieldLinear n e heN ho heF
  obtain ⟨c, hc⟩ := heP
  let u := binaryActionHom n c
  let d := Matrix.SpecialLinearGroup.toGL c
  let h := d⁻¹ * g * d
  have hh : binaryCongruence n h = u⁻¹ * e * u := by
    dsimp [h, d, u]
    rw [map_mul, map_mul, map_inv, binaryCongruence_toGL, hg]
  have hnormal : binaryCongruence n h ∈
      Subgroup.normalizer (pointParabolicImage n : Set (BinaryAut n)) ∨
      binaryCongruence n h ∈
      Subgroup.normalizer (planeParabolicImage n : Set (BinaryAut n)) := by
    rw [hh]
    exact hc.imp (mem_normalizer_of_conjugate _ u e) (mem_normalizer_of_conjugate _ u e)
  have horder : orderOf (binaryCongruence n h) = orderOf e := by
    rw [hh]
    simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj u⁻¹).orderOf_eq e
  have hodd : Odd (orderOf h) := odd_orderOf_of_odd_binaryCongruence n h (horder ▸ ho)
  have hbound := hexponent h hodd (hgeometry h hnormal)
  have hdiv := (orderOf_map_dvd (binaryCongruence n) h).trans hbound
  rwa [horder] at hdiv

end Representation.HermitianTensorThree.ParabolicTorus
