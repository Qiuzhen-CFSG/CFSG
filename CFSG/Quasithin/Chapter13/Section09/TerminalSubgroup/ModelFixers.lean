module

public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.Actions
public import Theory.SpecificGroups.PSL3Two.AlternatingFourFixer
public import Theory.SpecificGroups.AlternatingSix.AlternatingFourFixer

/-!
# Discharging the terminal subgroup's model fixers

The original residual is transported by its actual inclusion into the terminal
subgroup and the supplied model equivalence. The intrinsic model calculations
then give full centralization in PSL₃(2), and the quasithin contradiction in A₆.
No pointwise-fixer premise remains.

Source: Aschbacher–Smith, proof of 13.9.1, printed p.974 (PDF p.991).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup
open Subgroup
variable {G : Type*} [Group G]

private noncomputable def markedResidualEquiv
    {X : Type*} [Group X] (E M₂ : Subgroup G)
    (h₂ : residual M₂ ≤ terminal E)
    (e₂ : residual M₂ ≃* alternatingGroup (Fin 4)) (eH : terminal E ≃* X) :
    ((residual M₂).subgroupOf (terminal E)).map eH.toMonoidHom ≃*
      alternatingGroup (Fin 4) :=
  (((residual M₂).subgroupOf (terminal E)).equivMapOfInjective
    eH.toMonoidHom eH.injective).symm.trans
      ((subgroupOfEquivOfLe h₂).trans e₂)

/-- The original M₁ action centralizes the PSL₃(2) terminal subgroup. -/
theorem centralizes_of_psl3Two
    (E M₁ M₂ : Subgroup G) (hE : E = M₁.pCoreIn 2)
    (hcomm : M₁ ≤ centralizer (residual M₂ : Set G))
    (h₂ : residual M₂ ≤ terminal E)
    (e₂ : residual M₂ ≃* alternatingGroup (Fin 4))
    (eH : terminal E ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    M₁ ≤ centralizer (terminal E : Set G) := by
  apply centralizes_of_model_fixer_eq_bot E M₁ M₂ hE hcomm eH
  exact Matrix.PSL3Two.alternatingFour_fixer_eq_bot _
    (markedResidualEquiv E M₂ h₂ e₂ eH)

/-- The original A₄ residual and the A₆ terminal subgroup contradict quasithinness. -/
theorem false_of_alternating_six [Finite G]
    (hG : IsQuasithin G) (E M₁ M₂ : Subgroup G) (hE : E = M₁.pCoreIn 2)
    (hcomm : M₁ ≤ centralizer (residual M₂ : Set G))
    (h₂ : residual M₂ ≤ terminal E)
    (e₁ : residual M₁ ≃* alternatingGroup (Fin 4))
    (e₂ : residual M₂ ≃* alternatingGroup (Fin 4))
    (eH : terminal E ≃* alternatingGroup (Fin 6)) : False := by
  apply false_of_alternating_six_model_fixer hG E M₁ M₂ hE hcomm e₁ eH
  exact AlternatingSix.alternatingFour_fixer_isPGroup _
    (markedResidualEquiv E M₂ h₂ e₂ eH)

end CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup
