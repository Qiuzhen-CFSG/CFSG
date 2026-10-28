module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.LinearCoordinates

/-!
# Parameter identities needed for the common Ree field map

The additive map on the positive type VI block is already constructed from
the actual group automorphism. Three further identities remain: its scaled
multiplication law, the inverse scale on the negative type VI block, and the
two-parameter action on both type V blocks. `ParameterRelations` records
these explicit intermediate equations. Its witness must be proved from the
group relations; it is not part of the final field-recovery hypotheses.

Dividing the additive map by its value at one recovers a field equivalence.
The normalization theorem keeps both signs and the central Suzuki scale
`c * theta(c)^2`, as required by GLS3, Table 2.4, types V and VI, and
2.5.1(b,c), in `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
variable {m : ℕ}

/-- Positive and negative root characters are inverse units. -/
def signedScale (c : (CoefficientField m)ˣ) (positive : Bool) : (CoefficientField m)ˣ :=
  if positive then c else c⁻¹

/-- The character of the long root α + 2β in a type V block. -/
def centralScale (c : (CoefficientField m)ˣ) : (CoefficientField m)ˣ :=
  c * Units.map (theta m) c ^ 2

/-- The torus obtained from the two long simple-root scales and their short partners. -/
def blockTorus (b c : (CoefficientField m)ˣ) : TorusParameters m :=
  torusParametersOfSimpleScales ![b, c, Units.map (theta m) c, Units.map (theta m) b]

/-- The remaining root-character calculation, independent of any group automorphism.
It includes global twist compatibility, as well as the action on both literal words. -/
def TorusWordLaws (b c : (CoefficientField m)ˣ) : Prop :=
  TwistCompatible (blockTorus b c) ∧
  (∀ positive t,
    matrixTorusConj (blockTorus b c) (linearWord m positive t).val =
      (linearWord m positive ((signedScale b positive : CoefficientField m) * t)).val) ∧
  (∀ positive t u,
    matrixTorusConj (blockTorus b c) (suzukiWord m positive t u).val =
      (suzukiWord m positive ((signedScale c positive : CoefficientField m) * t)
        ((signedScale (centralScale c) positive : CoefficientField m) * u)).val)

namespace SuzukiCoordinates
variable {d : LocalBlockInput m} (C : SuzukiCoordinates d)

def element (positive : Bool) (t u : CoefficientField m) : d.fixedGroup :=
  ⟨suzukiWord m positive t u, C.suzuki_fixed positive t u⟩

theorem element_mem (positive : Bool) (t u : CoefficientField m) :
    C.element positive t u ∈ simpleBlock d .suzuki positive := C.suzuki_mem positive t u

theorem element_word (positive : Bool) (t u : CoefficientField m) :
    (C.element positive t u).val = suzukiWord m positive t u := rfl

theorem element_cover (positive : Bool) {x : d.fixedGroup}
    (hx : x ∈ simpleBlock d .suzuki positive) : ∃ t u, C.element positive t u = x := by
  obtain ⟨t, u, h⟩ := C.suzuki_cover positive x hx
  exact ⟨t, u, Subtype.ext h⟩

end SuzukiCoordinates

/-- Remaining identities for the concrete parameter maps. Proving this predicate
from pair and block preservation is the group-relations obligation. -/
def ParameterRelations (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d)
    (c : (CoefficientField m)ˣ) : Prop :=
  let f := linearParameterAut d a hb true
  (∀ t v, f (t * v) * f 1 = f t * f v) ∧
  (∀ t, a (linearElement d false t) =
    linearElement d false ((f 1)⁻¹ * (f t / f 1))) ∧
  (∀ positive t u, a (C.element positive t u) =
    C.element positive ((signedScale c positive : CoefficientField m) * (f t / f 1))
      ((signedScale (centralScale c) positive : CoefficientField m) * (f u / f 1)))

/-- Normalize the additive map after the group relations have forced multiplication.
This gives one field map on all four signed blocks, including the central parameter. -/
theorem exists_field_on_coordinates_of_relations
    (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d)
    (c : (CoefficientField m)ˣ) (h : ParameterRelations d a hb C c) :
    ∃ (b : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m),
      (∀ positive t, a (linearElement d positive t) =
        linearElement d positive ((signedScale b positive : CoefficientField m) * σ t)) ∧
      (∀ positive t u, a (C.element positive t u) =
        C.element positive ((signedScale c positive : CoefficientField m) * σ t)
          ((signedScale (centralScale c) positive : CoefficientField m) * σ u)) := by
  let f := linearParameterAut d a hb true
  obtain ⟨hmul, hneg, hsu⟩ := h
  have h1 : f 1 ≠ 0 := by
    intro hz
    exact one_ne_zero (f.injective (hz.trans (map_zero f).symm))
  obtain ⟨σ, hσ⟩ := exists_fieldEquiv_of_scaled_multiplicative f hmul
  have hdiv (t : CoefficientField m) : f t / f 1 = σ t := by
    rw [hσ t]
    exact mul_div_cancel_left₀ (σ t) h1
  refine ⟨Units.mk0 (f 1) h1, σ, ?_, ?_⟩
  · intro positive t
    cases positive
    · have he : (f 1)⁻¹ * (f t / f 1) =
          (signedScale (Units.mk0 (f 1) h1) false : CoefficientField m) * σ t := by
        rw [hdiv]
        rfl
      exact (hneg t).trans (congrArg (linearElement d false) he)
    · exact (linearParameterAut_action d a hb true t).trans
        (congrArg (linearElement d true) (hσ t))
  · intro positive t u
    exact (hsu positive t u).trans (congrArg₂ (C.element positive)
      (congrArg (fun z => (signedScale c positive : CoefficientField m) * z) (hdiv t))
      (congrArg (fun z => (signedScale (centralScale c) positive : CoefficientField m) * z)
        (hdiv u)))

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
end
