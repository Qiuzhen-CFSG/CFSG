module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneComparison

/-!
# Nontrivial complementary factors in B.5.11

If C_G(G₁) is trivial, the actual product in B.5.10 gives G=G₁≤LA.
The quotient by the selected normal component L is therefore a two-group.
Since O₂(G)=1, its generalized Fitting subgroup is precisely L. The full
earlier B.5.1 implication then proves the quasisimple alternative, contradicting
the counterexample hypothesis. This establishes the missing nontriviality
in B.5.11(1), together with the already proved faithful, offender-generated
complementary action and strict order descent.

The recursion theorem invokes classification only for that strictly smaller
centralizer on C_V(G₁). With a proved rank bound, the comparison theorem
retains the full quasisimple or S₃ output on that same action. Module extraction
in B.5.11(2) and the final exceptional assembly are separate obligations.

Earlier inputs are the complete universal B.5.1 and B.5.5 implications,
produced by qt-b05-quasisimple and qt-b05-quotient-components. Their final
discharge belongs to qt-b05-general-classification.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.11, p.109.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
open QuasisimpleSource
open PreliminaryActions.Preparation
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

omit [Finite G] in
/-- The selected first factor is contained in the actual subgroup LA. -/
theorem ComponentActionCase.first_le_sup {A L H : Subgroup G}
    {s : MovedSection ρ L} (hc : ComponentActionCase ρ A L s H) : H ≤ L ⊔ A := by
  cases hc with
  | linearTwo => exact le_sup_left
  | symmetricFive => exact le_rfl
  | doubleThree => exact le_sup_left
  | naturalThree => exact le_sup_left
  | fourCover => exact le_sup_left

/-- With no complementary factor, the selected component is all of F*(G).
This uses the original offender, not an unmarked model quotient. -/
theorem Conclusion.fitting_eq_of_second_eq_bot (c : Conclusion ρ)
    (hyp : FFHypothesis K ρ) (he : centralizer (c.first : Set G) = ⊥) :
    generalizedFitting G = c.component := by
  have hfirst : c.first = ⊤ := by
    simpa only [he, sup_bot_eq] using c.productConfiguration.product.sup_eq_top
  have hsup : c.component ⊔ c.offender = ⊤ := by
    apply top_unique
    rw [← hfirst]
    exact c.actionCase.first_le_sup ρ
  let : c.component.Normal := c.component_normal
  let : IsQuasisimple c.component := c.isComponent.2
  let : IsElementaryAbelian 2 c.offender := c.minimal.1.1.2
  have hquot : IsPGroup 2 (G ⧸ c.component) :=
    isPGroup_quotient_of_sup_eq_top _ _ (IsElementaryAbelian.isPGroup 2 c.offender) hsup
  exact generalizedFitting_eq_of_quasisimple_two_quotient _ hquot hyp.twoCore

/-- A trivial complement is already the full adequate quasisimple alternative.
The SQTK condition is derived from the complete B.5.5 model conclusion and
rank one, while the K-group property uses the original covering map. -/
theorem Conclusion.adequate_of_second_eq_bot (c : Conclusion ρ)
    (h5 : ComponentInput.{u,v} K)
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hr : primeRank 3 c.component = 1)
    (he : centralizer (c.first : Set G) = ⊥) : AdequateAlternative ρ := by
  have hf := c.fitting_eq_of_second_eq_bot ρ hyp he
  have hz : center G ≤ generalizedFitting G := by
    apply le_trans _ (fitting_le_generalizedFitting _)
    have hn : Group.IsNilpotent (center G) := by
      refine ⟨1, ?_⟩
      rw [Subgroup.upperCentralSeries_one_eq_top_iff]
      infer_instance
    exact le_sSup ⟨inferInstance, hn⟩
  have hs : IsSQTK K c.component :=
    ⟨component_stronglyQuasithin ρ h5 hyp c.isComponent hr,
      component_isKGroup ρ hyp c.component⟩
  have hfit : generalizedFitting G = c.component ⊔ center G := by
    rw [hf] at hz ⊢
    exact (sup_eq_left.mpr hz).symm
  obtain ⟨q⟩ := h1 G V ρ c.component
    ⟨hyp.finite_module, hyp.faithful, c.isComponent.2, hs,
      hfit, hyp.twoCore, hyp.generated⟩
  have hq : IsQuasisimple (generalizedFitting G) := hf.symm ▸ c.isComponent.2
  have ha : Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting G)) := by
    rw [hf]
    exact ⟨q⟩
  obtain ⟨a⟩ := ha
  exact Or.inr (.quasisimple hq a)

/-- B.5.11(1)'s nontriviality assertion under the actual counterexample condition. -/
theorem Conclusion.second_ne_bot (c : Conclusion ρ)
    (h5 : ComponentInput.{u,v} K)
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hr : primeRank 3 c.component = 1)
    (hnot : ¬ AdequateAlternative ρ) : centralizer (c.first : Set G) ≠ ⊥ :=
  fun he => hnot (c.adequate_of_second_eq_bot ρ h5 h1 hyp hr he)

/-- All of B.5.11(1), with every source hypothesis on the actual smaller
factor. In particular neither its nontriviality nor its order decrease is assumed. -/
theorem Conclusion.nontrivial_descent (c : Conclusion ρ)
    (h5 : ComponentInput.{u,v} K)
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hr : primeRank 3 c.component = 1)
    (hnot : ¬ AdequateAlternative ρ) :
    Nontrivial (centralizer (c.first : Set G)) ∧
      Nat.card (centralizer (c.first : Set G)) < Nat.card G ∧
      FFHypothesis K (c.productConfiguration.fixed.toRepresentation.comp
        (centralizer (c.first : Set G)).subtype) := by
  exact ⟨(Subgroup.nontrivial_iff_ne_bot _).mpr (c.second_ne_bot ρ h5 h1 hyp hr hnot),
    c.descent ρ hyp⟩

/-- The B.5.11 recursive call is made only on the strict smaller centralizer,
with nontriviality and all B.5.3 hypotheses established on its original action. -/
theorem Conclusion.classify_second (c : Conclusion ρ)
    (h5 : ComponentInput.{u,v} K)
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hr : primeRank 3 c.component = 1)
    (hnot : ¬ AdequateAlternative ρ)
    (ih : SmallerClassification.{u,v} K (Nat.card G)) :
    NontrivialAdequateAlternative (c.productConfiguration.fixed.toRepresentation.comp
      (centralizer (c.first : Set G)).subtype) := by
  obtain ⟨hn, hlt, hh⟩ := c.nontrivial_descent ρ h5 h1 hyp hr hnot
  let := hn
  exact (ih _ hlt _ _ hh).of_nontrivial _

/-- Actual consumer of the rank comparison in the B.5.11 recursive call.
The centralizer rank bound is still to be constructed from the SQTK cover. -/
theorem Conclusion.compare_second (c : Conclusion ρ)
    (h5 : ComponentInput.{u,v} K)
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hr : primeRank 3 c.component = 1)
    (hnot : ¬ AdequateAlternative ρ)
    (ih : SmallerClassification.{u,v} K (Nat.card G))
    (hsecond : primeRank 3 (centralizer (c.first : Set G)) ≤ 1) :
    (IsQuasisimple (generalizedFitting (centralizer (c.first : Set G))) ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
        (c.productConfiguration.fixed.toRepresentation.comp
          (centralizer (c.first : Set G)).subtype)
        (generalizedFitting (centralizer (c.first : Set G))))) ∨
      Nonempty (SymmetricThreeCase (c.productConfiguration.fixed.toRepresentation.comp
        (centralizer (c.first : Set G)).subtype)) :=
  (c.classify_second ρ h5 h1 hyp hr hnot ih).at_three_rank_le_one hsecond

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
