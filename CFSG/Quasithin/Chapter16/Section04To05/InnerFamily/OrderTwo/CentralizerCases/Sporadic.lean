module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Sporadic.Mathieu
public import Theory.Mathieu.M24.Properties.OuterRestriction

/-!
# The nine sporadic branches of the residual-centralizer alternative

The (E2)(iii) carrier enumeration is exhausted by actual model equivalences.
M₁₁ and M₂₄ are excluded by their proved automorphism innerness. The literal
16.1.5 innerness clauses for M₂₃, J₄ and Ru remain earlier-source inputs;
in particular a two-group outer quotient is not substituted for J₄ innerness.
The M₂₂ calculation keeps precisely the outer row excluded by 16.4.7.

Faithful central-quotient transport carries each remaining embedded residual
to its model fixer. The M₁₂ branch also constructs the A₅ marking and the
order-four lower bound inside H*, then uses the intrinsic upper bound and
square identities to obtain its whole E₄ centralizer.

`sporadic_alternative_of_calculations` assembles these implications. It is
conditional on the four intrinsic fixer calculations specified in `Contracts`;
it does not assert the completed source alternative. Their discharge and the
final sporadic assembly remain owned by this module.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
(E2)(iii), 16.1.5, 16.4.7 and proof of 16.4.9(1), printed pp.1170–1172,
1186 and 1189.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.Sporadic
open Subgroup Theory.GroupTheory OuterResidual ClassificationModels
open OtherPreliminaries.Mathieu
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
variable {S : Type*} [Group S]

/-- Genuine model involution innerness excludes the chosen outer element through every central cover. -/
theorem no_outer_of_model_inner
    (hG : HasEvenTypeCentralizers G) (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (e2 : (L ⧸ pCore 2 L) ≃* S)
    (inner : ∀ a : MulAut S, orderOf a = 2 → ∃ s, a = MulAut.conj s) : False := by
  let := h.component.quasisimple
  have hodd := component_oddCore hG h.toCentralComponentSetup
  let e := (LiePreliminaries.centerQuotientEquivTwoCore hodd).trans e2
  let hn := h.sylow_normalizes (h.le_sylow hr)
  exact modelAction_outer L e r hn hout
    (inner _ ((modelAction_order L e h hr).trans hr2))

/-- The proved full automorphism innerness of M₂₄ excludes its quotient branch. -/
theorem no_m24
    (hG : HasEvenTypeCentralizers G) (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (e2 : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M24) : False := by
  apply no_outer_of_model_inner hG h hr hr2 hout e2
  intro a _
  obtain ⟨s, hs⟩ := Sporadic.Mathieu.M24OuterRestriction.conj_surjective a
  exact ⟨s, hs.symm⟩

/-- Transport an intrinsic bound on the embedded model residual, retaining the cover kernel. -/
theorem alternative_of_outer_residual_fixer
    (hG : HasEvenTypeCentralizers G) (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (e2 : (L ⧸ pCore 2 L) ≃* S)
    (fixer : OuterResidualFixerBound S) : ResidualCentralizerAlternative T L r := by
  let : Finite S := Finite.of_equiv (L ⧸ pCore 2 L) e2.toEquiv
  let := h.component.quasisimple
  have hodd := component_oddCore hG h.toCentralComponentSetup
  let e := (LiePreliminaries.centerQuotientEquivTwoCore hodd).trans e2
  let hn := h.sylow_normalizes (h.le_sylow hr)
  apply alternative_of_fixer_not_four_dvd L e h hr hr2
  rw [modelResidual_eq_fixedTwoResidual L e r hn hodd]
  have hsimple : IsSimpleGroup S :=
    (MulEquiv.isSimpleGroup_congr e).mp IsQuasisimple.simple
  have hperfect : Group.IsPerfect S :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact fixer hsimple hperfect _ ((modelAction_order L e h hr).trans hr2)
    (modelAction_outer L e r hn hout)

/-- The M₂₂ residual calculation applies after precisely the source outer-class exclusion. -/
theorem m22_alternative_of_fixer
    (hG : HasEvenTypeCentralizers G) (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (e2 : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M22)
    (excluded : ∀ e : (L ⧸ center L) ≃* Sporadic.Mathieu.M22,
      ¬ M22ExcludedRow (modelAction L e
        (actionElement L r (h.sylow_normalizes (h.le_sylow hr)))))
    (fixer : M22FixerCalculation) : ResidualCentralizerAlternative T L r := by
  let := h.component.quasisimple
  have hodd := component_oddCore hG h.toCentralComponentSetup
  let e := (LiePreliminaries.centerQuotientEquivTwoCore hodd).trans e2
  let hn := h.sylow_normalizes (h.le_sylow hr)
  apply alternative_of_fixer_not_four_dvd L e h hr hr2
  rw [modelResidual_eq_fixedTwoResidual L e r hn hodd]
  exact fixer _ ((modelAction_order L e h hr).trans hr2)
    (modelAction_outer L e r hn hout) (excluded e)

/-- Exhaustive nine-carrier reduction with the four remaining intrinsic calculations explicit. -/
theorem sporadic_alternative_of_calculations
    {K : GroupClass} (hG : Hypothesis1611 K G) (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hspor : IsEvenTypeSporadicQuotient (L ⧸ pCore 2 L))
    (m23_inner : ∀ a : MulAut Sporadic.Mathieu.M23,
      orderOf a = 2 → ∃ s, a = MulAut.conj s)
    (j4_inner : ∀ a : MulAut Janko4.Model,
      orderOf a = 2 → ∃ s, a = MulAut.conj s)
    (ru_inner : ∀ a : MulAut Rudvalis.Model,
      orderOf a = 2 → ∃ s, a = MulAut.conj s)
    (m12_table : ∀ a : MulAut Sporadic.Mathieu.M12,
      orderOf a = 2 → M12InvolutionAlternative a)
    (m22_excluded : ∀ e : (L ⧸ center L) ≃* Sporadic.Mathieu.M22,
      ¬ M22ExcludedRow (modelAction L e
        (actionElement L r (h.sylow_normalizes (h.le_sylow hr)))))
    (m12_fixer : M12FixerCalculation) (m22_fixer : M22FixerCalculation)
    (j2_fixer : OuterResidualFixerBound Sporadic.LeechRelated.J2.Carrier)
    (hs_fixer : OuterResidualFixerBound Sporadic.LeechRelated.HS.Carrier) :
    ResidualCentralizerAlternative T L r := by
  obtain ⟨name, hj3, hhe, ⟨e⟩⟩ := hspor
  cases name with
  | m11 => exact (no_m11 hG.evenType h hr hr2 hout e).elim
  | m12 =>
    obtain ⟨hcard, helem, hcase⟩ := mathieu_twelve_of_table_and_fixer
      hG.evenType h hr hr2 hout e m12_table m12_fixer
    exact Or.inr ⟨hcard, helem, Or.inr hcase⟩
  | m22 => exact m22_alternative_of_fixer hG.evenType h hr hr2 hout e m22_excluded m22_fixer
  | m23 => exact (no_outer_of_model_inner hG.evenType h hr hr2 hout e m23_inner).elim
  | m24 => exact (no_m24 hG.evenType h hr hr2 hout e).elim
  | j2 => exact alternative_of_outer_residual_fixer hG.evenType h hr hr2 hout e j2_fixer
  | j3 => exact (hj3 rfl).elim
  | j4 => exact (no_outer_of_model_inner hG.evenType h hr hr2 hout e j4_inner).elim
  | hs => exact alternative_of_outer_residual_fixer hG.evenType h hr hr2 hout e hs_fixer
  | he => exact (hhe rfl).elim
  | ru => exact (no_outer_of_model_inner hG.evenType h hr hr2 hout e ru_inner).elim

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.Sporadic
