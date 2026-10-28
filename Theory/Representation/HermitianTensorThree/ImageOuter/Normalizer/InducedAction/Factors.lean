module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Contracts
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
/-!
# Standard factors for automorphisms of the Hermitian image

Conjugation in the literal binary normalizer transports through the actual
image equivalences: the image is SL₃ in even half-degree and PSL₃ in odd
half-degree. Binary-field automorphism coverage and faithful lifting from
the central quotient give a GL₃, coefficient, and opposition-graph
factorization in both cases. Congruence and coefficient actions realize
the first two factors on the given Hermitian space.

The remaining exclusion of a graph intertwiner is a separate representation
calculation. Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.4.2 setup and H.4.4(7), printed pp.380–381; GLS3, Theorem 2.5.12.
-/

public section
open Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions.SixCommutators
open Matrix.PSL3.CartanActions.ActorCoverage
open Representation.HermitianTensorThree
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter
variable (n : ℕ) [NeZero n]

private def imageNormalizerAction (e : binaryNormalizer n) : MulAut (Image n) :=
  MulAut.congr (binaryImageEquiv n).symm ((binaryImage n).normalizerMonoidHom e)

private theorem imageNormalizerAction_apply (e : binaryNormalizer n) (a : Cover n) :
    binaryEquiv n (imageNormalizerAction n e (toImage n a)).val =
      e.val * binaryActionHom n a * e.val⁻¹ := by
  have h : binaryImageEquiv n (imageNormalizerAction n e (toImage n a)) =
      (binaryImage n).normalizerMonoidHom e (binaryImageEquiv n (toImage n a)) := by
    simp [imageNormalizerAction]
  exact congrArg Subtype.val h

private theorem image_standard_factors (α : MulAut (Image n)) :
    ∃ (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (τ : E n ≃+* E n) (ε : Bool),
      ∀ a : Cover n, α (toImage n a) = toImage n (specialActor (E n) g τ ε a) := by
  have hc := standard_eq_top_of_two_power_card (E n)
    (show 0 < 2 * n from Nat.mul_pos (by decide) (Nat.pos_of_ne_zero (NeZero.ne n))) (card_E n)
  rcases Nat.even_or_odd n with hn | hn
  · let k := imageEquivSL n hn
    obtain ⟨g, τ, ε, h⟩ := specialCoverage_of_standard_eq_top (E n) hc (MulAut.congr k α)
    refine ⟨g, τ, ε, fun a => k.injective ?_⟩
    have hk (a : Cover n) : k (toImage n a) = a := imageEquivSL_toImage n hn a
    calc
      k (α (toImage n a)) = (MulAut.congr k α) (k (toImage n a)) := by simp
      _ = specialActor (E n) g τ ε a := by rw [h, hk]
      _ = k (toImage n (specialActor (E n) g τ ε a)) := (hk _).symm
  · let k := imageEquivPSL n hn
    obtain ⟨g, τ, ε, h⟩ := projectiveCoverage_of_standard_eq_top (E n) hc (MulAut.congr k α)
    refine ⟨g, τ, ε, fun a => k.injective ?_⟩
    have hk (a : Cover n) : k (toImage n a) = QuotientGroup.mk a :=
      imageEquivPSL_toImage n hn a
    calc
      k (α (toImage n a)) = (MulAut.congr k α) (k (toImage n a)) := by simp
      _ = projectiveActor (E n) g τ ε (QuotientGroup.mk a) := by rw [h, hk]
      _ = QuotientGroup.mk (specialActor (E n) g τ ε a) := by
        rw [← centerAction_specialActor, centerAction_mk]
      _ = k (toImage n (specialActor (E n) g τ ε a)) := (hk _).symm

/-- The induced action has standard factors on the original cover in both parity cases. -/
theorem normalizer_standard_factors (e : Space n ≃ₗ[ZMod 2] Space n)
    (he : e ∈ binaryNormalizer n) :
    ∃ (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (τ : E n ≃+* E n) (ε : Bool),
      ∀ a : Cover n, e * binaryActionHom n a * e⁻¹ =
        binaryActionHom n (specialActor (E n) g τ ε a) := by
  obtain ⟨g, τ, ε, h⟩ := image_standard_factors n (imageNormalizerAction n ⟨e, he⟩)
  refine ⟨g, τ, ε, fun a => ?_⟩
  have ha := congrArg (fun x : Image n => binaryEquiv n x.val) (h a)
  rw [imageNormalizerAction_apply] at ha
  exact ha

/-- GL₃ conjugation is implemented by the literal Hermitian congruence. -/
theorem binaryCongruence_conj (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (a : Cover n) :
    binaryCongruence n g * binaryActionHom n a * (binaryCongruence n g)⁻¹ =
      binaryActionHom n (linearConjSL (E n) g a) := by
  rw [← binaryCongruence_toGL n (linearConjSL (E n) g a), linearConjSL_toGL, map_mul, map_mul, map_inv,
    binaryCongruence_toGL]

/-- The complete linear-coefficient factor is implemented on the binary space. -/
theorem semilinearCongruence_conj (g : Matrix.GeneralLinearGroup (Fin 3) (E n))
    (τ : E n ≃+* E n) (a : Cover n) :
    semilinearCongruence n g τ * binaryActionHom n a * (semilinearCongruence n g τ)⁻¹ =
      binaryActionHom n (specialActor (E n) g τ false a) := by
  change (binaryCongruence n g * coefficient n τ) * binaryActionHom n a *
    (binaryCongruence n g * coefficient n τ)⁻¹ = _
  rw [mul_inv_rev]
  have h : binaryCongruence n g * coefficient n τ * binaryActionHom n a *
      ((coefficient n τ)⁻¹ * (binaryCongruence n g)⁻¹) =
      binaryCongruence n g * (coefficient n τ * binaryActionHom n a * (coefficient n τ)⁻¹) *
        (binaryCongruence n g)⁻¹ := by simp only [mul_assoc]
  rw [h, coefficient_conj, binaryCongruence_conj]
  rfl

end Representation.HermitianTensorThree.ImageOuter
