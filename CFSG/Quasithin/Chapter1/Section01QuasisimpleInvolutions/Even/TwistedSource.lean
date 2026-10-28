module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.Triality
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.Inner
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.Source

/-!
# Triality and Tits source branches of 1.1.5

The genuine triality root-lift calculations cover both q=2 and q>=4.
Their two-primary kernel exclusion suffices for the marked involution:
innerness and odd-core inversion make the original center a two-group.
For the simple Tits endpoint the compatible Parrott lifts give the complete
universal-kernel vanishing. Both proofs retain the original automorphism.

Source: Aschbacher--Smith 1.1.5(3)(a), printed pp.501--503, and I.1.3;
GLS3 §6.1 for the two-primary covering calculations.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- Every genuine binary triality parameter gives the full marked source conclusion. -/
theorem MarkedInvolution.triality_source (d : MarkedInvolution α P) {f : ℕ}
    (hf : 1 ≤ f) (h : Triality.Standard.IsTrialityGroupAt (2 ^ f) (L ⧸ center L)) :
    ModelAction115 L α := by
  have hi := d.triality_inner hf h
  apply d.lie_of_center_eq_bot (.inr (.inl (.triality f hf h))) hi
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f (by omega)).mp h
  apply d.center_eq_bot_of_odd_universal_kernel hi e
  by_cases hlarge : 2 ≤ f
  · exact Triality.Standard.CentralCovers.TwoPrimary.universal_not_two_dvd_kernel_of_two_le
      f (by omega) hlarge
  · have he : f = 1 := by omega
    subst f
    exact Triality.Standard.CentralCovers.TwoPrimary.smallField_universal_not_two_dvd_kernel

/-- The endpoint is the genuine simple Parrott Tits group, with no lift premise. -/
theorem MarkedInvolution.tits_source (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* Tits.ParrottGroup) : ModelAction115 L α := by
  have hi := d.tits_inner e
  apply d.lie_of_center_eq_bot (.inr (.inl (.tits ⟨e⟩))) hi
  exact center_eq_bot_of_centralQuotientEquiv
    Tits.CentralCoverLifting.CompatibleGenerators.universalProjection_ker_eq_bot e

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
