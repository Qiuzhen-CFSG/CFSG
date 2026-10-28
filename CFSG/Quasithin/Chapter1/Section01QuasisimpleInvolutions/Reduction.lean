module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.ClassicalSource
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.OrdinarySource
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.TwistedSource
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.ReeSource
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.SporadicSource

/-!
# Source-family reduction for the marked involution classification

Inspect the full Theorem C list using the original marked involution.
Every alternating, odd-characteristic, Bender and binary-linear family gives
the full six-constructor action conclusion. The rank-two arguments include
all genuine triality fields, the derived endpoints, and Tits. Ordinary Ree
parameters are settled by their actual two-primary cover exclusion, and
Rudvalis by the proved stabilizer realization.

The initial reduction records field-eight Ree and Held alternatives. The
actual ambient class-two calculation then discharges field-eight Ree, leaving
only Held in `source_reduction_he`. The complete conclusion still awaits
Held permutation realization; no family conclusion is assumed.
Source: Aschbacher--Smith 1.1.5(3), printed pp.501--503.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ChapterA.Section02
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- All rank-two cases except the literal field-eight Ree quotient are settled. -/
theorem MarkedInvolution.rankTwo_source_reduction (d : MarkedInvolution α P) {f : ℕ}
    (h : IsTheoremCRankTwoModel (L ⧸ center L) f) :
    ModelAction115 L α ∨ Nonempty (L ⧸ center L ≃* ReeF4.Model 1) := by
  cases h with
  | linear hf h => exact .inl (d.linearThree_source hf h)
  | symplectic hf h => exact .inl (d.symplecticFour_modelAction hf h)
  | g2 hf h => exact .inl (d.g2_modelAction hf h)
  | triality hf h => exact .inl (d.triality_source hf h)
  | ree_f4 m hm _ iso =>
    obtain ⟨e⟩ := iso
    by_cases hlarge : 2 ≤ m
    · exact .inl (d.ree_source_of_two_le hlarge e)
    · have he : m = 1 := by omega
      exact .inr ⟨he ▸ e⟩
  | symplectic_derived _ iso =>
    obtain ⟨e⟩ := iso
    exact .inl (Alternating.projective_derived d e)
  | g2_derived _ iso =>
    obtain ⟨e⟩ := iso
    exact .inl (d.g2Derived_source e)
  | tits _ iso =>
    obtain ⟨e⟩ := iso
    exact .inl (d.tits_source e)

/-- Original marked hypotheses and the full Theorem C list leave exactly the
field-eight Ree and Held source branches. No family conclusion is assumed. -/
theorem MarkedInvolution.source_reduction (d : MarkedInvolution α P)
    (h : IsTheoremCModel (L ⧸ center L)) :
    ModelAction115 L α ∨ Nonempty (L ⧸ center L ≃* ReeF4.Model 1) ∨
      Nonempty (L ⧸ center L ≃* Held.He) := by
  cases h with
  | alternating n hn iso =>
    obtain ⟨e⟩ := iso
    exact .inl (d.alternating_source hn e)
  | odd h => exact .inl (d.odd_source h)
  | bender h => exact .inl (d.bender_source h)
  | rank_two f h =>
    rcases d.rankTwo_source_reduction h with hm | hr
    · exact .inl hm
    · exact .inr (.inl hr)
  | linear_binary n hn h => exact .inl (d.binary_source hn h)
  | sporadic h =>
    rcases d.sporadic_reduction h with hm | hh | hr
    · exact .inl hm
    · exact .inr (.inr hh)
    · obtain ⟨e⟩ := hr
      exact .inl (d.modelAction_ru e)


/-- The ambient field-eight source calculation completes every rank-two case. -/
theorem MarkedInvolution.rankTwo_source (d : MarkedInvolution α P) {f : ℕ}
    (h : IsTheoremCRankTwoModel (L ⧸ center L) f) : ModelAction115 L α := by
  rcases d.rankTwo_source_reduction h with hm | hr
  · exact hm
  · obtain ⟨e⟩ := hr
    exact d.ree_source (by decide) e

/-- The original marked hypotheses and the full model list leave only the
actual Held quotient carrier, whose realization is the remaining producer. -/
theorem MarkedInvolution.source_reduction_he (d : MarkedInvolution α P)
    (h : IsTheoremCModel (L ⧸ center L)) :
    ModelAction115 L α ∨ Nonempty (L ⧸ center L ≃* Held.He) := by
  rcases d.source_reduction h with hm | hr | hh
  · exact .inl hm
  · obtain ⟨e⟩ := hr
    exact .inl (d.ree_source (by decide) e)
  · exact .inr hh

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
