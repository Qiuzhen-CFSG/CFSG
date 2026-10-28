module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.NormalizedPresentation

/-!
# Centrality of the normalized Parrott relators

Each original relator commutes with every named generator by one of the 370
centrality relations of `NormalizedPresentation`. Free-word induction extends
this to every element of that presentation. This proves centrality only;
none of the original relators is set equal to one by this argument.

Source: Parrott (1972), §5, p.683, relations I–VIII, with commutator
`a⁻¹ * b⁻¹ * a * b`; the auxiliary presentation is defined in the imported module.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators
open scoped commutatorElement

set_option backward.isDefEq.respectTransparency false in
/-- All original relator values are central in the auxiliary presentation. -/
theorem normalizedGenerator_relators_central (j : ParrottRelatorIndex) :
    FreeGroup.lift normalizedGenerator (parrottRelator j) ∈
      Subgroup.center NormalizedPresentation := by
  let z := FreeGroup.lift normalizedGenerator (parrottRelator j)
  have hg (i : ParrottGenerator) : Commute z (normalizedGenerator i) := by
    have hm : FreeGroup.lift normalizedGenerator = PresentedGroup.mk normalizedRelatorSet := by
      ext k
      rfl
    have hh : FreeGroup.lift normalizedGenerator (normalizedRelator (.inl (j, i))) = 1 := by
      rw [hm]
      exact PresentedGroup.one_of_mem ⟨.inl (j, i), rfl⟩
    have hh' : ⁅z⁻¹, (normalizedGenerator i)⁻¹⁆ = 1 := by
      simpa only [normalizedRelator, parrottCommutator, map_mul, map_inv,
        FreeGroup.lift_apply_of, commutatorElement_def, inv_inv] using hh
    simpa only [inv_inv] using (commutatorElement_eq_one_iff_commute.mp hh').inv_inv
  apply Subgroup.mem_center_iff.mpr
  intro x
  have h : Commute z x := by
    induction x using PresentedGroup.induction_on with
    | H w =>
      induction w using FreeGroup.induction_on with
      | C1 => simpa only [map_one] using Commute.one_right z
      | of i => exact hg i
      | inv_of i hi => simpa only [map_inv] using hi.inv_right
      | mul u v hu hv => simpa only [map_mul] using hu.mul_right hv
  exact h.symm.eq

/-- The four Weyl conjugation equations left after the two odd-power arguments.
The braid equation remains a separate obligation. -/
@[expose] def isRemainingWeylConjugation : ParrottRelatorIndex → Bool
  | .vii_s4 | .vii_s3 | .vii_r3 | .viii_s2 => true
  | _ => false

end Tits.CentralCoverLifting.CompatibleGenerators
