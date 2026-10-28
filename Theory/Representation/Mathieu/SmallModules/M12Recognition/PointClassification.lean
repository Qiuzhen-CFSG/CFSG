module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.GeneratorReduction
public import Theory.Representation.Mathieu.SmallModules.M12Recognition

/-!
# Assembly of degree-ten binary M₁₁ recognition

The comparison with the eleven-point augmentation module is an actual
M₁₁-equivariant equivalence. The remaining recognition problem separates
into classification on the actual C₁₁:C₅ normalizer and conjugacy of the
remaining standard-involution matrix by a normalizer-module automorphism.
Coordinate transport and actual M₁₁ generation combine these two inputs and
supply the literal point-restriction equivalence required by M₁₂
recognition.

The inputs remain explicit in this reduction module. Import
`PointClassification.Completeness` for the unconditional degree-ten M₁₁
classification and its application to the literal M₁₂ point restriction.
That extension combines both independent producers without an import cycle.

Source application: Aschbacher--Smith, G.7.3(2), printed p.348 (PDF p.359),
citing G. D. James, *The modular characters of the Mathieu groups*,
J. Algebra 27 (1973), 57--111.
-/

public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification
open Sporadic.Mathieu

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Combine normalizer classification with conjugacy of the remaining involution. Faithful
representations of degree ten already satisfy the needed irreducibility.
Neither classification premise is asserted by this conditional theorem. -/
theorem equiv_point_of_normalizer_inputs (σ : Representation (ZMod 2) M11 V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 10)
    (hlocal : ∀ τ : Representation (ZMod 2) m11Sylow11Normalizer V,
      Function.Injective τ → Module.finrank (ZMod 2) V = 10 →
      Nonempty (τ.Equiv normalizerRepresentation))
    (hextension : ∀ τ : Representation (ZMod 2) M11 M12Heart,
      Function.Injective τ → τ.IsIrreducible →
      (∀ g : m11Sylow11Normalizer, τ g.val = pointRepresentation g.val) →
      ∃ e : normalizerRepresentation.Equiv normalizerRepresentation,
        e.toLinearMap.comp (τ m11GeneratorAInM11) =
          (pointRepresentation m11GeneratorAInM11).comp e.toLinearMap) :
    Nonempty (σ.Equiv pointRepresentation) := by
  obtain ⟨e⟩ := hlocal (σ.comp m11Sylow11Normalizer.subtype)
    (hf.comp Subtype.val_injective) hd
  have hfaith := normalizerCoordinateRepresentation_injective σ hf e.toLinearEquiv
  have hirr := irreducible_of_eleven_dvd
    (normalizerCoordinateRepresentation σ e.toLinearEquiv) hfaith finrank_m12Heart.le
    (by rw [m11_order]; norm_num)
  have hon := normalizerCoordinateRepresentation_on_normalizer σ e
  obtain ⟨f, hfA⟩ := hextension (normalizerCoordinateRepresentation σ e.toLinearEquiv)
    hfaith hirr hon
  exact ⟨(normalizerCoordinateEquiv σ e.toLinearEquiv).trans
    (equivOfNormalizerAndInvolution _ hon f hfA)⟩

/-- Application to the parent's literal M₁₁ restriction. This discharges its
faithfulness and dimension using the existing M₁₂ reduction, and feeds the
result to the published M₁₂ assembly. All three classification inputs remain
explicit until their independent producers have been proved. -/
theorem isM12Heart_of_normalizer_inputs [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) M12 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 10)
    (hlocal : ∀ τ : Representation (ZMod 2) m11Sylow11Normalizer V,
      Function.Injective τ → Module.finrank (ZMod 2) V = 10 →
      Nonempty (τ.Equiv normalizerRepresentation))
    (hm11 : ∀ τ : Representation (ZMod 2) M11 M12Heart,
      Function.Injective τ → τ.IsIrreducible →
      (∀ g : m11Sylow11Normalizer, τ g.val = pointRepresentation g.val) →
      ∃ e : normalizerRepresentation.Equiv normalizerRepresentation,
        e.toLinearMap.comp (τ m11GeneratorAInM11) =
          (pointRepresentation m11GeneratorAInM11).comp e.toLinearMap)
    (hm12 : ∀ τ : Representation (ZMod 2) M12 M12Heart,
      Function.Injective τ → τ.IsIrreducible →
      (∀ g : M11, τ (pointEmbedding g) = m12HeartRepresentation (pointEmbedding g)) →
      IsM12Heart τ) : IsM12Heart ρ := by
  apply isM12Heart_of_point_inputs ρ hf _ hm12
  exact equiv_point_of_normalizer_inputs (ρ.comp pointEmbedding)
    (hf.comp pointEmbedding_injective) (finrank_eq_ten ρ hf hd) hlocal hm11

end Representation.MathieuSmall.M12Recognition.PointClassification
