module
public import Theory.GroupTheory.PGroup.SmallFrattiniSingularIndex
public import Theory.Representation.UniformBinaryFiveSingularBound
public import Theory.SpecificGroups.MinusExtraspecial.Recognition

/-!
# The five-point closure is the minus extraspecial group

The literal five-point quadratic orbit forces every elementary subgroup
to have order below eight. The intrinsic order-thirty-two classification
then identifies the group with Q8 * D8. This supplies the core model for
the field-four row of Aschbacher–Smith 14.2.16 and I.4.7.
-/

public section
open scoped IsMulCommutative
namespace SmallFrattini
open Subgroup Module
variable {Q : Type*} [Group Q] [Finite Q] [IsExtraspecial 2 Q]

theorem minus_model_of_five_quadratic_orbit
    (htwo : IsPGroup 2 Q) (hphi : Nat.card (frattini Q) = 2)
    (hcard : Nat.card Q = 32) :
    letI := quotientElementary htwo
    ∀ (f : UniformBinaryPolar.V 5 →ₗ[ZMod 2] Additive (Q ⧸ frattini Q)),
      (quotientBilinearForm htwo hphi).comp f f = UniformBinaryPolar.form 5 →
      (∀ i, quotientQuadraticForm htwo hphi (f (Pi.single i 1)) = 0) →
      Nonempty (Q ≃* MinusExtraspecial.Model) := by
  let := quotientElementary htwo
  intro f hp hcoord
  apply IsExtraspecial.exists_mulEquiv_minusExtraspecial_model ?_ hcard
  intro A hA
  let := hA
  by_contra hn
  have hlarge : 8 ≤ Nat.card A := by omega
  have hindex : A.index ≤ 2^2 := by
    have hh := A.card_mul_index
    rw [hcard] at hh
    nlinarith
  obtain ⟨E,hE,_,hd⟩ := exists_totallySingular_of_index htwo hphi A 2 hindex
  have hpolar : (quotientQuadraticForm htwo hphi).polarBilin.compl₁₂ f f =
      UniformBinaryPolar.form 5 := by
    rw [quotientQuadraticForm_polar]
    exact hp
  have hh := UniformBinaryPolar.five_orbit_singular_codimension_ge_three
    (quotientQuadraticForm htwo hphi) f hpolar hcoord E hE
  omega
end SmallFrattini
