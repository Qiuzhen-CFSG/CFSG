module

public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.SpecificGroups.PSL3Three.InnerInvolutionCentralizer
public import Theory.SpecificGroups.LinearCoefficientEquiv

/-!
# Odd-characteristic and sporadic component preliminaries

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
of 1 March 2004, 16.1.2, 16.1.5 and 16.1.6, printed pp.1170–1172.

The completed cases here are the M₁₁ involutory-automorphism calculation and
the inner PSL₃(3) calculation. Their proofs transport the checked concrete
centralizers through actual model isomorphisms. For a perfect M₁₁ cover the
quotient fixed subgroup is computed without assuming fixed points lift.

The remaining automorphism tables and covering restrictions are not asserted.
In particular the M₁₁ quotient calculation alone does not prove that a perfect
cover with this quotient has trivial center; that needs its multiplier result.
-/

public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries

open Subgroup Theory.GroupTheory Sporadic.Mathieu

variable {L : Type*} [Group L]

/-- Identify the exact three-element-field model in (E2)(ii). -/
theorem equiv_pslThree_of_isPSL (hL : ClassicalGroup.IsPSL L 3 3) :
    Nonempty (L ≃* Matrix.PSL3Three.PSL) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  let _ : Fintype F := Fintype.ofFinite F
  let eF : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF.symm)⟩

/-- The PSL₃(3) alternative in (E2)(ii) has no central covering kernel,
as needed when restricting the nonsimple list in 16.1.2. -/
theorem pslThree_center_eq_bot (hL : ClassicalGroup.IsPSL L 3 3) : center L = ⊥ := by
  obtain ⟨e⟩ := equiv_pslThree_of_isPSL hL
  apply (center L).eq_bot_iff_card.mpr
  calc
    Nat.card (center L) = Nat.card (center Matrix.PSL3Three.SL) :=
      Nat.card_congr (centerCongr (e.trans Matrix.PSL3Three.equiv.symm)).toEquiv
    _ = 1 := (center Matrix.PSL3Three.SL).eq_bot_iff_card.mp Matrix.PSL3Three.center_eq_bot

/-- The inner alternative of 16.1.5(1), with the full fixed subgroup C_L(r). -/
theorem pslThree_inner_involution (hL : ClassicalGroup.IsPSL L 3 3)
    (r : MulAut L) (hr : orderOf r = 2) (hi : ∃ g : L, r = MulAut.conj g) :
    Nonempty (r.fixedSubgroup ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) := by
  obtain ⟨e⟩ := equiv_pslThree_of_isPSL hL
  exact ⟨(MulAut.fixedSubgroupCongr e r).trans
    (Matrix.PSL3Three.innerInvolutoryAutFixedEquiv _
      (((MulAut.congr e).orderOf_eq r).trans hr) ((MulAut.congr_inner_iff e r).mpr hi))⟩

/-- Both assertions in 16.1.5(3) for the full M₁₁ group. -/
theorem m11_involution (e : L ≃* M11) (r : MulAut L) (hr : orderOf r = 2) :
    (∃ g : L, r = MulAut.conj g) ∧
      Nonempty (r.fixedSubgroup ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
  ⟨automorphism_inner_of_equiv_m11 e r, ⟨involutoryAutFixedEquivOfM11 e r hr⟩⟩

/-- Quotient centralizer data from the actual (E2)(iii) input. This also applies
before triviality of the covering kernel has been established. -/
theorem m11_quotient_involution [Finite L] [IsQuasisimple L]
    (hO : pPrimeCore 2 L = ⊥) (e : L ⧸ pCore 2 L ≃* M11)
    (r : MulAut L) (hr : orderOf r = 2) :
    (∃ g : L, r = MulAut.conj g) ∧
      Nonempty (QuotientCentralizer r ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) := by
  have hZ : center L = pCore 2 L := IsQuasisimple.center_eq_pCore hO
  let eZ := (QuotientGroup.quotientMulEquivOfEq hZ).trans e
  exact ⟨automorphism_inner_of_central_quotient_m11 eZ r,
    ⟨involutoryAutQuotientFixedEquivOfM11 eZ r hr⟩⟩

/-- The M₁₁ quotient case of 16.1.6, for arbitrary two-elements. In fact every
automorphism of such a perfect cover is inner. -/
theorem m11_sylow_centralizing_two_automorphisms [Finite L] [IsQuasisimple L]
    (hO : pPrimeCore 2 L = ⊥) (e : L ⧸ pCore 2 L ≃* M11) :
    HasInnerSylowCentralizingTwoAutomorphisms L := by
  have hZ : center L = pCore 2 L := IsQuasisimple.center_eq_pCore hO
  let eZ := (QuotientGroup.quotientMulEquivOfEq hZ).trans e
  intro r _ _ _ _
  exact automorphism_inner_of_central_quotient_m11 eZ r

end CFSG.Quasithin.Chapter16.OtherPreliminaries
