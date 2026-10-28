module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.Construction
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model

/-!
# Application of the explicit elementary-nine central extension

`ThreeCover.Construction` supplies a finite perfect permutation group and an
actual central subgroup isomorphic to C₃ × C₃. An isomorphism from its quotient
to the literal field-nine projective SU image supplies the required cover.

The quotient comparison remains an explicit hypothesis here. Consequently this
module is not yet an unconditional proof of the exceptional lower cover in
Aschbacher–Smith I.1.4(5), printed p.408 (`refs/quasithin.pdf`, PDF p.419), or
GLS3 Table 6.1.3. It does prove every covering and kernel assertion once that
concrete comparison is supplied; no group order or family tag replaces it.
-/

public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover

open PerfectCentralCovering
open Theory.SpecificGroups.ClassicalUnitary

/-- Transport of the constructed cover along an actual quotient identification. -/
def coverOfModelEquiv (e : Projective ≃* UnitaryFourThree.Carrier 4) :
    Cover Carrier (UnitaryFourThree.Carrier 4) where
  toMonoidHom := e.toMonoidHom.comp quotientCover.toMonoidHom
  surjective := e.surjective.comp quotientCover.surjective
  isPerfect := carrierPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact quotientCover.ker_le_center

/-- The transported map retains exactly the displayed nine-element kernel. -/
noncomputable def kernelEquivOfModelEquiv (e : Projective ≃* UnitaryFourThree.Carrier 4) :
    (coverOfModelEquiv e).toMonoidHom.ker ≃* KernelCoordinates :=
  (MulEquiv.subgroupCongr
    (MonoidHom.ker_comp_of_injective _ _ e.injective)).trans quotientKernelEquiv

/-- The literal PSU₄(3) consumer of the remaining quotient comparison. -/
theorem exists_cover_of_model_equiv
    (h : Nonempty (Projective ≃* UnitaryFourThree.Carrier 4)) :
    ∃ (E : Type) (_ : Group E) (_ : Finite E),
      ∃ f : Cover E (UnitaryFourThree.Carrier 4),
        Nonempty (f.toMonoidHom.ker ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) := by
  obtain ⟨e⟩ := h
  exact ⟨Carrier, inferInstance, carrier_finite, coverOfModelEquiv e,
    ⟨kernelEquivOfModelEquiv e⟩⟩

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover
