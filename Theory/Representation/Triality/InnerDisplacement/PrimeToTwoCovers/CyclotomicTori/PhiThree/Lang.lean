module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree.Weyl
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve.Lang

/-!
# The cubic Lang witness in the literal split triality group

The finite Geck group is compared with the concrete Clifford Spin group over
an algebraic closure.  Spin Lang surjectivity gives a solution of the
graph-field equation.  Since the twisting word is fixed and has cube one, the
solution is fixed by the ordinary cubic Frobenius.  The proved finite-field
coordinate descent and rational-root generation then put it back in the
literal split Geck group.  This handles every positive exponent, including
the parameters divisible by three; no coefficients from the special `q = 2`
certificate are reused.

Source: GLS3 §2.2 and §6.1 (`refs/KGroup/GLS3/chapter2.tex`), together with
the concrete Spin comparison and finite-field descent in
`Theory.Representation.Triality.BinaryDegree.CarrierTransport`.
-/

@[expose] public section
noncomputable section

namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree

open Triality.Standard
open Triality.BinaryDegree.CarrierTransport
open Triality.BinaryDegree.CarrierTransport.GeckSpin
open Triality.SimplyConnected
open Triality.SimplyConnected.GraphField
open Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve

/- The algebraic-closure route is independent of the particular presentation
   of the cubic extension. -/
theorem exists_langWitness_of_pos (n : ℕ) (hn : 0 < n) :
    ∃ x : SplitGroup (binaryParameters n hn),
      graphFieldAutomorphism (binaryParameters n hn) x =
        x * twistWord n hn := by
  let k := AlgebraicClosure (ExtensionField (binaryParameters n hn))
  let f := coefficientEmbedding k n hn
  let e := finiteComparison k f
  let t : Points k := e (twistWord n hn)
  have htfix : sigma k n t = t := by
    have h := finiteComparison_graphField k f (twistWord n hn)
    have hw := graphField_twistWord n hn
    change e (graphFieldAutomorphism (binaryParameters n hn) (twistWord n hn)) =
      sigma k n (e (twistWord n hn)) at h
    rw [hw] at h
    exact h.symm
  have htcube : t ^ 3 = 1 := by
    change e (twistWord n hn) ^ 3 = 1
    rw [← map_pow, twistWord_cube, map_one]
  obtain ⟨y, hy⟩ := graphField_lang_surjective k n hn t
  have hy' : sigma k n y = t⁻¹ * y := by
    have h := congrArg Inv.inv hy
    simp only [mul_inv_rev, inv_inv] at h
    calc
      sigma k n y = (sigma k n y * y⁻¹) * y := by group
      _ = t⁻¹ * y := by rw [h]
  have hx : sigma k n (y⁻¹) = y⁻¹ * t := by
    rw [map_inv, hy']
    group
  have hx2 : sigma k n (sigma k n (y⁻¹)) = sigma k n (y⁻¹) * t := by
    calc
      sigma k n (sigma k n (y⁻¹)) = sigma k n (y⁻¹ * t) :=
        congrArg (sigma k n) hx
      _ = sigma k n (y⁻¹) * sigma k n t := by rw [map_mul]
      _ = sigma k n (y⁻¹) * t := by rw [htfix]
  have hx_cube : sigma k n (sigma k n (sigma k n (y⁻¹))) = y⁻¹ := by
    calc
      sigma k n (sigma k n (sigma k n (y⁻¹))) =
          sigma k n (sigma k n (y⁻¹) * t) := by rw [hx2]
      _ = sigma k n (sigma k n (y⁻¹)) * sigma k n t := by rw [map_mul]
      _ = sigma k n (sigma k n (y⁻¹)) * t := by rw [htfix]
      _ = (sigma k n (y⁻¹) * t) * t := by rw [hx2]
      _ = ((y⁻¹ * t) * t) * t := by rw [hx]
      _ = y⁻¹ * t ^ 3 := by simp [pow_three, mul_assoc]
      _ = y⁻¹ := by rw [htcube, mul_one]
  have hfixed : frobeniusPointAut k (3 * n) (y⁻¹) = y⁻¹ := by
    rw [← sigma_cube k n (y⁻¹)]
    exact hx_cube
  have hcoordinates := (frobenius_fixed_iff_coordinates f (y⁻¹)).mp hfixed
  have hrational : y⁻¹ ∈ rationalSimpleSubgroup f :=
    rational_generation f (y⁻¹) hcoordinates
  have hrange : y⁻¹ ∈ e.range := by
    rw [finiteComparison_range k f]
    exact hrational
  obtain ⟨x, hxval⟩ := hrange
  refine ⟨x, ?_⟩
  apply finiteComparison_injective k f
  calc
    e (graphFieldAutomorphism (binaryParameters n hn) x) =
        sigma k n (e x) := finiteComparison_graphField k f x
    _ = sigma k n (y⁻¹) := by rw [hxval]
    _ = y⁻¹ * t := hx
    _ = e x * e (twistWord n hn) := by rw [hxval, ← show t = e (twistWord n hn) from rfl]
    _ = e (x * twistWord n hn) := (map_mul e x (twistWord n hn)).symm

/-- The requested witness, with the source's large-parameter hypothesis. -/
theorem exists_langWitness (n : ℕ) (hn : 0 < n) (_hlarge : 1 < n) :
    ∃ x : SplitGroup (binaryParameters n hn),
      graphFieldAutomorphism (binaryParameters n hn) x =
        x * twistWord n hn :=
  exists_langWitness_of_pos n hn

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree
