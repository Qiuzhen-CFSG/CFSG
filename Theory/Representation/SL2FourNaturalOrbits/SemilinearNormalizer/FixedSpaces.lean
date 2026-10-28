module

public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Basic

/-!
# Fixed planes of conjugates of coordinate Frobenius

Conjugation transports the fixed subspace by the conjugating linear map.
The coordinate fixed space has four elements, so every such conjugate fixes
an actual binary plane. This is the fixed-space part of the field-type
calculation in Aschbacher--Smith 6.2.5, combined manuscript (1 March 2004),
printed pp.680--681 (PDF pp.697--698). Classification of all field-coset
involutions is a separate assertion.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourNatural.SemilinearNormalizer
open Matrix
open Matrix.GeneralLinearGroup
/-- Conjugating the coordinate field involution transports its fixed plane
by the same binary linear map. -/
theorem conjugate_fieldFixed (e : BinaryGL) :
    (e * frobeniusLinear * e⁻¹).toLinearMap.fixedSubmodule =
      fieldFixed.map e.toLinearMap := by
  ext v
  constructor
  · intro h
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    change frobeniusLinear (e.symm v) = e.symm v
    apply e.injective
    change e (frobeniusLinear (e.symm v)) = v at h
    simpa only [e.apply_symm_apply] using h
  · rintro ⟨w, hw, rfl⟩
    change e (frobeniusLinear (e.symm (e w))) = e w
    rw [e.symm_apply_apply]
    change frobeniusLinear w = w at hw
    rw [hw]

/-- Every conjugate of coordinate Frobenius has a four-element fixed space. -/
theorem card_conjugate_fieldFixed (e : BinaryGL) :
    Nat.card (e * frobeniusLinear * e⁻¹).toLinearMap.fixedSubmodule = 4 := by
  rw [conjugate_fieldFixed]
  exact (Nat.card_congr
    (Submodule.equivMapOfInjective e.toLinearMap e.injective fieldFixed).toEquiv).symm.trans
      card_fieldFixed

/-- The actual field-type plane attached to a conjugate field involution. -/
def conjugateFieldPlane (e : BinaryGL) : Plane :=
  ⟨(e * frobeniusLinear * e⁻¹).toLinearMap.fixedSubmodule, card_conjugate_fieldFixed e⟩

theorem conjugateFieldPlane_centralized (e : BinaryGL) (v : V)
    (hv : v ∈ (conjugateFieldPlane e).val) :
    (e * frobeniusLinear * e⁻¹) v = v := hv

end Representation.SL2FourNatural.SemilinearNormalizer
