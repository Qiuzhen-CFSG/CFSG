module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HallJanko.SourceDegree.Reduction
public import Theory.Representation.JankoTwo.SmallBinaryDegrees

/-!
# Source applications of the small-degree J₂ calculations

The absolute catalogue and its one cubic fixed-space calculation feed the
literal `hspectrum` and `hdisplacement` inputs of the source degree reduction.
The displacement proof retains the actual ambient group and its center-free
component marking and handles outer involutions by cubic inversion.

Both modular representation calculations remain explicit, unproved inputs.
These conditional source applications do not complete the source theorem.
The cover, degree-window, and final source assembly remain with SourceDegree.

Source: Guralnick--Malle, Proposition 5.1, manuscript p.16; Aschbacher--Smith,
Chapter K.4 opening, printed pp.457--458.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HallJanko
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.JankoTwo.SmallBinaryDegrees
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
variable {ρ : Representation (ZMod 2) G W}

omit [Finite G] in
/-- Apply scalar descent on the original source module through the actual
center-free component marking. This is the `hspectrum` application. -/
theorem SourceHypotheses.finrank_cases_of_absolute_calculations
    (h : SourceHypotheses ρ)
    (e : generalizedFitting G ≃* _root_.Sporadic.LeechRelated.J2.Carrier)
    (hd : Module.finrank (ZMod 2) W ≤ 32)
    (hcalc : AbsoluteWindowCalculations.{v}) :
    Module.finrank (ZMod 2) W = 12 ∨ Module.finrank (ZMod 2) W = 28 :=
  h.finrank_cases_of_small_degree_spectrum e hd
    (Representation.JankoTwo.SmallBinaryDegrees.finrank_cases_of_absolute_calculations hcalc)

/-- The source degree-28 branch has no small-displacement involution, including
outside the component. The proof does not use the source cubic-ratio hypothesis. -/
theorem SourceHypotheses.involution_displacement_of_absolute_calculations
    (h : SourceHypotheses ρ)
    (hz : center (generalizedFitting G) = ⊥)
    (e : generalizedFitting G ≃* _root_.Sporadic.LeechRelated.J2.Carrier)
    (hcalc : AbsoluteWindowCalculations.{v}) (hcubic : CubicFixedSpaceCalculations.{v})
    (hd : Module.finrank (ZMod 2) W = 28)
    (t : G) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    10 ≤ fixedCodim ρ (zpowers t) := by
  let := h.fitting_simple_of_center_eq_bot hz
  exact involution_displacement_of_cubic_bound ρ e h.faithful h.irreducible
    (fun σ hf hi => cubic_displacement_of_absolute_calculations hcalc hcubic σ hf hi hd)
    t ht ht2

/-- Supply precisely the spectrum and displacement inputs of the existing
source assembly. The absolute catalogue and cubic calculation still need proofs. -/
theorem SourceHypotheses.center_eq_bot_and_finrank_of_absolute_calculations
    (h : SourceHypotheses ρ)
    (hc : IsPGroup 2 (center (generalizedFitting G)))
    (hr : primeRank 2 (MulAut _root_.Sporadic.LeechRelated.J2.Carrier) ≤ 4)
    (hgen : InvolutionConjugateGenerationBound (generalizedFitting G) 4)
    (hcalc : AbsoluteWindowCalculations.{v}) (hcubic : CubicFixedSpaceCalculations.{v}) :
    center (generalizedFitting G) = ⊥ ∧ Module.finrank (ZMod 2) W = 12 := by
  have hz := h.fitting_center_eq_bot_of_twoGroup hc
  obtain ⟨e⟩ := h.fitting_equiv_of_center_eq_bot hz
  exact h.center_eq_bot_and_finrank_of_model_inputs hc hr hgen
    (Representation.JankoTwo.SmallBinaryDegrees.finrank_cases_of_absolute_calculations hcalc)
    (fun hd => h.involution_displacement_of_absolute_calculations hz e hcalc hcubic hd)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HallJanko
