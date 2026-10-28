module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.Models
public import Theory.Representation.FiniteFieldSemilinearDisplacement

/-!
# The coefficient-field involution branch

An offender containing an involution that acts nontrivially and semilinearly
on a finite coefficient field forces binary dimension at most twice the
offender rank. Semilinear descent gives exactly half-dimensional fixed space;
containment in the offender compares the two fixed codimensions.

For the odd symplectic degree estimate this gives `q^r ≤ 4 * rank A + 1`.
The theorem uses the actual full-normalizer operators on the original space.
The coefficient field, its involution, semilinearity and the degree estimate
remain explicit; no Schur-field or symplectic classification is assumed.

This is an auxiliary step for the cross-characteristic exclusion in
Guralnick–Malle I, Proposition 4.5. The fixed-dimension formula is the
order-two case of finite-field semilinear descent.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal.HigherSymplecticParameters
variable {L W F : Type*} [Group L] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Module F W] [FiniteDimensional F W]

private theorem dimension_le_twice_rank
    (σ : Representation (ZMod 2) L W) (A : Subgroup (linearNormalizer σ))
    (hA : IsOffender (normalizerRepresentation σ) A)
    (t : linearNormalizer σ) (ht : t ∈ A) (ht2 : orderOf t = 2)
    (τ : F ≃+* F) (hτ : orderOf τ = 2)
    (hsemi : ∀ (a : F) (v : W), (normalizerRepresentation σ) t (a • v) =
      τ a • (normalizerRepresentation σ) t v) :
    Module.finrank (ZMod 2) W ≤ 2 * rank A := by
  have hdim := Representation.FiniteFieldSemilinearDisplacement.fixedCodim_formula
    (normalizerRepresentation σ) (by decide : 0 < 2) t ht2 τ hτ hsemi
  have htower := Module.finrank_mul_finrank (ZMod 2) F W
  have hle : fixedSpace (normalizerRepresentation σ) A ≤
      fixedSpace (normalizerRepresentation σ) (zpowers t) := by
    intro v hv a
    exact hv ⟨a, (zpowers_le.mpr ht) a.property⟩
  have hfix := Submodule.finrank_mono hle
  have ha := fixedCodim_add_finrank (normalizerRepresentation σ) A
  have ht' := fixedCodim_add_finrank (normalizerRepresentation σ) (zpowers t)
  have ho := hA.2
  norm_num at hdim
  nlinarith

/-- An actual field involution in the source offender strengthens the coarse
symplectic parameter bound, with the degree estimate still explicit. -/
theorem symplectic_power_le_of_semilinear_offender
    (σ : Representation (ZMod 2) L W) (A : Subgroup (linearNormalizer σ))
    (hA : IsOffender (normalizerRepresentation σ) A)
    (t : linearNormalizer σ) (ht : t ∈ A) (ht2 : orderOf t = 2)
    (τ : F ≃+* F) (hτ : orderOf τ = 2)
    (hsemi : ∀ (a : F) (v : W), (normalizerRepresentation σ) t (a • v) =
      τ a • (normalizerRepresentation σ) t v)
    {r q : ℕ} (hdegree : q ^ r ≤ 2 * Module.finrank (ZMod 2) W + 1) :
    q ^ r ≤ 4 * rank A + 1 := by
  have := dimension_le_twice_rank σ A hA t ht ht2 τ hτ hsemi
  omega
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal.HigherSymplecticParameters
