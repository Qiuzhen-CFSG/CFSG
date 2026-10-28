module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.Inner
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary
public import Theory.SpecificGroups.G2.MultiplierOrdinary
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import GorensteinWalter.PSL2EvenDefiningKernel

/-!
# Completed even-family branches of 1.1.5

The Sylow-fixer calculations force innerness, so odd-core inversion makes the
center a two-group. The actual universal-kernel calculations exclude this
center for PSL₂(q), q ≥ 8, for Sp₄(q), q ≥ 4, and for PSL₅(2).
For G₂(q) the ordinary multiplier vanishes, whereas q = 4 permits the source
two-cover row. PSL₃(4) permits the same row without any multiplier calculation.

Every result concludes the canonical model/action alternative on the original
group and automorphism, with no additional cover or fixer premise.
Source: Aschbacher--Smith, 1.1.5(3)(a),(b), printed pp.501--502, and I.1.3.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels

variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- The ordinary binary rank-one branch, including q = 8. -/
theorem MarkedInvolution.linearTwo_modelAction (d : MarkedInvolution α P) {f : ℕ}
    (hf : 3 ≤ f) (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2 ^ f)) :
    ModelAction115 L α := by
  have hi := d.linearTwo_inner h
  apply d.lie_of_center_eq_bot (.inl (.linear f (by omega) h)) hi
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have he : Even (Nat.card F) := by
    rw [hF]
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : f ≠ 0))
  have hpow : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hf
  apply d.center_eq_bot_of_odd_universal_kernel hi e
  simpa only [ringChar.eq F 2] using
    GorensteinWalter.PSL2Cover.defining_prime_not_dvd_universal_kernel_of_even F he
      (by omega)

/-- PSL₃(4) and all its compatible nontrivial two-covers are allowed. -/
theorem MarkedInvolution.linearThreeFour_modelAction (d : MarkedInvolution α P)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) : ModelAction115 L α :=
  d.exceptional_of_inner (.inl h) (d.linearThree_inner (f := 2) (by decide) h)

/-- The full nonbinary symplectic-four branch, including q = 4. -/
theorem MarkedInvolution.symplecticFour_modelAction (d : MarkedInvolution α P) {f : ℕ}
    (hf : 2 ≤ f) (h : ClassicalGroup.IsPSp (L ⧸ center L) 2 (2 ^ f)) :
    ModelAction115 L α := by
  have hi := d.symplecticFour_inner hf h
  apply d.lie_of_center_eq_bot (.inr (.inl (.symplectic f hf h))) hi
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hpow : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hf
  exact d.center_eq_bot_of_odd_universal_kernel hi
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
    (Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.not_two_dvd_universal_kernel
      (by omega))

/-- The entire ordinary even G₂ family: q = 4 permits nontrivial two-covers,
and the actual universal kernel eliminates them at every larger field. -/
theorem MarkedInvolution.g2_modelAction (d : MarkedInvolution α P) {f : ℕ}
    (hf : 2 ≤ f) (h : IsG2At (L ⧸ center L) (2 ^ f)) : ModelAction115 L α := by
  have hi := d.g2_inner hf h
  by_cases htwo : f = 2
  · subst f
    exact d.exceptional_of_inner (.inr h) hi
  · apply d.lie_of_center_eq_bot (.inr (.inl (.g2 f hf h))) hi
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    exact center_eq_bot_of_centralQuotientEquiv
      (Atlas.G2.MultiplierOrdinary.even_universalProjection_ker_eq_bot_of_card_pow hF
        (by omega)) e

/-- PSL₅(2) has no nontrivial perfect central cover, by its actual universal
projection. This completes the n = 5 binary higher-linear branch. -/
theorem MarkedInvolution.binaryFive_modelAction (d : MarkedInvolution α P)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 5 2) : ModelAction115 L α := by
  have hi := d.binaryLinear_inner (.inr rfl) h
  apply d.lie_of_center_eq_bot (.inr (.inr ⟨5, .inr rfl, h⟩)) hi
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  exact center_eq_bot_of_centralQuotientEquiv
    (Theory.SpecificGroups.PSL5Two.UniversalCover.field_universalProjection_ker_eq_bot F hF) e

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
