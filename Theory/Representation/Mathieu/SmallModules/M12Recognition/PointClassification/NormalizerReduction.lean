module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.AugmentationModel
public import Theory.Mathieu.M11.Properties.PrimeNormalizers

/-!
# Coordinates on the actual Sylow-eleven normalizer in M₁₁

The normalizer is the already constructed subgroup `m11Sylow11Normalizer`,
with its literal inclusion in M₁₁. Its reference action is the restriction
of the twelve-point heart. The augmentation comparison proves that this
reference is faithful; the order-eleven argument proves irreducibility.

An equivalence on the normalizer transports the entire M₁₁ action to
coordinates in which the two normalizer actions agree. The classification
of the normalizer module and rigidity of extensions remain separate inputs.

Source application: the James completeness input to Aschbacher--Smith,
G.7.3(2), printed p.348 (PDF p.359). The normalizer and its multiplier-four
complement are proved in `Theory.Mathieu.M11.Properties.PrimeNormalizers`.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification
open Sporadic.Mathieu

/-- Restriction to the literal subgroup C₁₁:C₅, without changing its marking. -/
noncomputable def normalizerRepresentation :
    Representation (ZMod 2) m11Sylow11Normalizer M12Heart :=
  pointRepresentation.comp m11Sylow11Normalizer.subtype

theorem normalizerRepresentation_injective : Function.Injective normalizerRepresentation :=
  pointRepresentation_injective.comp Subtype.val_injective

theorem normalizerRepresentation_isIrreducible : normalizerRepresentation.IsIrreducible :=
  irreducible_of_eleven_dvd normalizerRepresentation normalizerRepresentation_injective
    finrank_m12Heart.le (by rw [m11Sylow11_normalizer_card]; norm_num)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) M11 V)

/-- Transport the full M₁₁ action through a linear equivalence. -/
noncomputable def normalizerCoordinateRepresentation (e : V ≃ₗ[ZMod 2] M12Heart) :
    Representation (ZMod 2) M11 M12Heart where
  toFun g := e.conj (σ g)
  map_one' := by ext v; simp [LinearEquiv.conj_apply]
  map_mul' g h := by ext v; simp [LinearEquiv.conj_apply, map_mul]

/-- The same coordinate change intertwines the full action. -/
noncomputable def normalizerCoordinateEquiv (e : V ≃ₗ[ZMod 2] M12Heart) :
    σ.Equiv (normalizerCoordinateRepresentation σ e) :=
  .mk e (by intro g; ext v; simp [normalizerCoordinateRepresentation, LinearEquiv.conj_apply])

theorem normalizerCoordinateRepresentation_injective (hf : Function.Injective σ)
    (e : V ≃ₗ[ZMod 2] M12Heart) :
    Function.Injective (normalizerCoordinateRepresentation σ e) := by
  intro g h he
  exact hf (e.conj.injective he)

/-- An equivalence on C₁₁:C₅ gives literal agreement there after transport. -/
theorem normalizerCoordinateRepresentation_on_normalizer
    (e : Representation.Equiv (σ.comp m11Sylow11Normalizer.subtype) normalizerRepresentation)
    (g : m11Sylow11Normalizer) :
    normalizerCoordinateRepresentation σ e.toLinearEquiv g.val = pointRepresentation g.val := by
  apply LinearMap.ext
  intro v
  change e (σ g.val (e.symm v)) = pointRepresentation g.val v
  have h := LinearMap.congr_fun (e.isIntertwining' g) (e.symm v)
  change e (σ g.val (e.symm v)) = pointRepresentation g.val (e (e.symm v)) at h
  simpa only [Representation.Equiv.apply_symm_apply] using h

end Representation.MathieuSmall.M12Recognition.PointClassification
