module
public import Theory.GroupTheory.PGroup.SmallFrattiniLinearForms
public import Theory.Representation.UniformBinaryQuadraticRadical

/-!
# Elementary centers from singular Frattini radicals

For a finite two-group with Frattini subgroup of order two, the radical
of its literal commutator form is the center image. If the square form
vanishes on that radical, every central element has square one. The
uniform five- and nine-point realizations provide this condition while
retaining the full center.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace SmallFrattini
variable {Q : Type*} [Group Q] [Finite Q]

/-- Singularity of the actual Frattini polar radical says precisely that
all elements of the center have square one. -/
theorem center_elementary_of_singular_radical
    (htwo : IsPGroup 2 Q) (hphi : Nat.card (frattini Q) = 2) :
    letI := quotientElementary htwo
    (∀ x : Additive (Q ⧸ frattini Q),
      x ∈ (quotientBilinearForm htwo hphi).ker →
        quotientQuadraticForm htwo hphi x = 0) →
      IsElementaryAbelian 2 (center Q) := by
  let := quotientElementary htwo
  intro hsing
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro z
  let x := QuotientGroup.mk' (frattini Q) z.val
  have hxc : x ∈ centerImage Q := ⟨z.val,z.property,rfl⟩
  have hx : Additive.ofMul x ∈ (quotientBilinearForm htwo hphi).ker := by
    apply LinearMap.mem_ker.mpr
    ext y
    exact (quotientBilinearForm_radical htwo hphi x).mpr hxc y
  have hs := hsing (Additive.ofMul x) hx
  rw [quotientQuadraticForm_apply] at hs
  have hsq : quotientSquare htwo hphi x = 1 := by
    apply (binaryMark hphi).injective
    rw [(binaryMark hphi).map_one]
    exact congrArg Additive.toMul hs
  apply Subtype.ext
  have he := congrArg (fun a : frattini Q => a.val) hsq
  rw [quotientSquare_apply_mk] at he
  exact he

/-- Apply the singular-radical calculation to the literal square and
commutator forms on a Frattini quotient, without deleting a central factor. -/
theorem center_elementary_of_uniform_quadratic_quotient
    (htwo : IsPGroup 2 Q) (hphi : Nat.card (frattini Q) = 2)
    (n : ℕ) (hn : n = 5 ∨ n = 9) :
    letI := quotientElementary htwo
    ∀ (f : UniformBinaryPolar.V n →ₗ[ZMod 2] Additive (Q ⧸ frattini Q)),
      Function.Surjective f →
      (quotientBilinearForm htwo hphi).comp f f = UniformBinaryPolar.form n →
      (∀ i, quotientQuadraticForm htwo hphi (f (Pi.single i 1)) = 0) →
      IsElementaryAbelian 2 (center Q) := by
  let := quotientElementary htwo
  intro f hf hp hcoord
  apply center_elementary_of_singular_radical htwo hphi
  intro x hx
  have hpolar : (quotientQuadraticForm htwo hphi).polarBilin.compl₁₂ f f =
      UniformBinaryPolar.form n := by
    rw [quotientQuadraticForm_polar]
    exact hp
  exact UniformBinaryPolar.radical_singular_of_uniform_pullback
    (quotientQuadraticForm htwo hphi) f hf hpolar hcoord hn x
    (by rwa [quotientQuadraticForm_polar])
end SmallFrattini
