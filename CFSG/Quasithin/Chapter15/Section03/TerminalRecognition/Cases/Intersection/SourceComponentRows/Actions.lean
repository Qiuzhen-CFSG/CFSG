module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceClassifications
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.OuterGroupComparison

/-!
# Corrected source actions on the terminal offender

The B.5.6 product branches contradict quasisimplicity of ambient F*.
The surviving B.5.1 extension clause retains its literal action and
identifies the Thompson image only when the offender actor is quasisimple.

The proofs adapt the existing terminal `ComponentRows` comparison to the
full `ProjectiveLine.QuasisimpleSourceConclusion`. The two-dimensional
F₄ offender clause remains on the original action; no legacy clause is
constructed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1/B.5.6,
printed pp.99–105; F.6.18, pp.309–310; K.1.3, p.453; final proof of
15.3.1, p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives

namespace SourceComponentRows

private theorem source_actor_cases {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (hL : IsQuasisimple (generalizedFitting D))
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting D)) :
    IsQuasisimple D ∨
      (∃ n, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (D ≃* Equiv.Perm (Fin n))) ∨
      Nonempty (D ≃* Atlas.G2.Model (ZMod 2)) := by
  have full (ht : generalizedFitting D = ⊤) : IsQuasisimple D := by
    let _ := hL
    exact IsQuasisimple.of_mulEquiv ((MulEquiv.subgroupCongr ht).trans topEquiv)
  cases c.clause_one with
  | irreducible _ _ _ _ h =>
    rcases h with ht | ⟨_, h⟩
    · exact Or.inl (full ht)
    · rcases h with hs | hg
      · obtain ⟨n, hlo, hhi, ⟨e⟩⟩ := hs
        exact Or.inr (Or.inl ⟨n, hlo, hhi, ⟨e.groupEquiv⟩⟩)
      · obtain ⟨e⟩ := hg
        exact Or.inr (Or.inr ⟨e.groupEquiv⟩)
  | doubleThree _ ht _ _ _ => exact Or.inl (full ht)
  | naturalDual _ _ ht _ => exact Or.inl (full ht)
  | repeatedNatural _ _ _ _ _ ht _ => exact Or.inl (full ht)

end SourceComponentRows

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)
include d

/-- The source actor cases preserve both the actual isomorphisms and the
Thompson equality in the quasisimple-actor branch. They assert no ambient equality. -/
theorem source_offender_actor_of_quasisimple_source
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup)) :
    (IsQuasisimple d.offenderGroup ∧
      (thompsonGroup H).map coreProjection = d.offenderGroup) ∨
      (∃ n, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (d.offenderGroup ≃* Equiv.Perm (Fin n))) ∨
      Nonempty (d.offenderGroup ≃* Atlas.G2.Model (ZMod 2)) := by
  rcases SourceComponentRows.source_actor_cases d.offenderAction
    (d.offender_fitting_quasisimple hL) c with h | h
  · exact Or.inl ⟨h, d.thompson_image_eq_quasisimple_offender h⟩
  · exact Or.inr h

/-- The corrected B.5.6 input forces its full quasisimple action branch
when the ambient F* is quasisimple. The outer-shape exclusion uses only
the actual commuting factors and their relative normality. -/
theorem source_offender_quasisimple_of_classifications
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (hB : SourceFFAlternative d.offenderAction) :
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup)) := by
  rcases hB with hB | ⟨c⟩
  · cases hB with
    | trivial h =>
      let _ := h
      apply (d.offender_ne_bot ?_).elim
      apply le_bot_iff.mp
      intro x hx
      exact Subgroup.mem_bot.mpr
        (congrArg Subtype.val (Subsingleton.elim (⟨x,hx⟩ : d.offenderGroup) 1))
    | quasisimple _ c => exact ⟨c⟩
    | symmetricThree c =>
      exact (d.thompson_image_not_symmetricThree hL
        (d.thompsonEquivSymmetricThree c.equiv)).elim
    | twoFactors c =>
      exact (ProductComparison.sourceTwoFactor_not_quasisimple
        (quotientAction V d.centralizer_isTwoGroup d.core_centralizes) c hL).elim
    | outerSixThree c =>
      exact (ProductComparison.outerSixThree_not_quasisimple
        (quotientAction V d.centralizer_isTwoGroup d.core_centralizes) c hL).elim
    | hyperplane c =>
      exact (ProductComparison.hyperplane_not_quasisimple
        (quotientAction V d.centralizer_isTwoGroup d.core_centralizes) c hL).elim
  · obtain ⟨c⟩ := c
    exact (OuterGroupComparison.outerShape_not_quasisimple
      (quotientAction V d.centralizer_isTwoGroup d.core_centralizes) c hL).elim

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
