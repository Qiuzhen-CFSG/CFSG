module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Branches
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.FixedComponent
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Source
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Endpoints

/-!
# Rank-two quotient inspection in the six-component enlargement

The small symplectic-derived and G₂-derived endpoints are excluded outright.
For the remaining constructors, the theorem below connects the exact source
configuration to intrinsic fixed-component calculations. The symplectic branch
retains the genuine Sp₄(4) field involution, transports the entire marked action
through its recognizing equivalence, and retains the full source configuration
for the separate field-case calculation.

This is a conditional assembly: the four contracts in `RankTwo.Inputs` remain
to be proved. It does not assert `RankTwoExclusion` without those premises.
This module owns their discharge; the containing quotient-recognition module
continues to own the full Theorem C catalogue assembly.

Source: Aschbacher–Smith, Theorem C, printed p.33, E.6.8, pp.247–248,
and E.6.23, p.254 (PDF p.265), combined manuscript of 1 March 2004.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
universe u
variable {G : Type u} [Group G] [Finite G]

/-- All eight source constructors are connected to the model calculations.
The intrinsic premises are outstanding obligations, not source hypotheses. -/
theorem rankTwoExclusion_of_inspections
    (hlinear : RankTwo.LinearInspection.{u})
    (hsymplectic : RankTwo.SymplecticInspection.{u})
    (hexceptional : RankTwo.ExceptionalInspection.{u})
    (T : Sylow 2 G) (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hfield : RankTwo.SymplecticFieldSourceExclusion T M V) :
    RankTwoExclusion T M V := by
  intro h h15 earlier U A L X g d hne Y hY f hm
  let _ := extension_quasisimple hY
  let _ : IsSimpleGroup (Y ⧸ center Y) := IsQuasisimple.simple
  obtain ⟨s, hs⟩ := RankTwo.quotient_fixed_six_action h d hY
  have he (hm : (∃ f : ℕ, 2 ≤ f ∧
        ClassificationModels.IsG2At (Y ⧸ center Y) (2 ^ f)) ∨
      (∃ f : ℕ, 1 ≤ f ∧
        Triality.Standard.IsTrialityGroupAt (2 ^ f) (Y ⧸ center Y)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty ((Y ⧸ center Y) ≃* ReeF4.Model m)) ∨
      Nonempty ((Y ⧸ center Y) ≃* Tits.ParrottGroup)) : False :=
    hexceptional _ hm s.involution s.involution_order s.six s.component s.model
  cases hm with
  | linear hf iso =>
    exact hlinear _ f hf iso s.involution s.involution_order s.six s.component s.model
  | symplectic hf iso =>
    obtain ⟨F, hF, hfin, hchar, hcard, e, he⟩ :=
      hsymplectic _ f hf iso s.involution s.involution_order s.six s.component s.model
    apply hfield h h15 earlier U A L X g d hne Y hY F hcard e
    rw [← hs, MonoidHom.map_zpowers]
    exact congrArg zpowers he
  | g2 hf iso => exact he (Or.inl ⟨f, hf, iso⟩)
  | triality hf iso => exact he (Or.inr (Or.inl ⟨f, hf, iso⟩))
  | ree_f4 m hm _hf iso => exact he (Or.inr (Or.inr (Or.inl ⟨m, hm, iso⟩)))
  | symplectic_derived _hf iso =>
    exact RankTwo.not_symplectic_derived d hY iso.some
  | g2_derived _hf iso => exact RankTwo.not_g2_derived d hY iso.some
  | tits _hf iso => exact he (Or.inr (Or.inr (Or.inr iso)))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
