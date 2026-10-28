module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Basic

/-!
# The full B.5.1 extension clause on the actual offender actor

The source conclusion makes its quasisimple F* either the whole actor,
or supplemented by each Sylow two-subgroup. Thus its quotient is a
two-group. A proper extension is literally Sₙ for 5 ≤ n ≤ 8 or G₂(2),
through the original module's action equivalence. In the full-component
case, the surviving commutator identifies the Thompson and offender actors.

The full `QuasisimpleSourceConclusion` is an explicit input here. Selecting
it from B.5.6 in the quasisimple ambient case remains a separate obligation;
these helpers do not replace the original B-side action witness.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.1(1), printed p.99; final proof of 15.3.1, printed p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace ComponentRows

/-- Every B.5.1 action case gives the two-group quotient above its actual F*. -/
theorem source_offender_quotient {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (c : QuasisimpleSourceConclusion ρ (generalizedFitting D)) :
    IsPGroup 2 (D ⧸ generalizedFitting D) := by
  cases c.clause_one with
  | irreducible _ _ _ _ h =>
    rcases h with ht | ⟨ht, _⟩
    · exact quotient_of_fitting_top ht
    · let T : Sylow 2 D := Classical.choice inferInstance
      exact isPGroup_quotient_of_sup_eq_top _ _ T.isPGroup' (ht T)
  | doubleThree _ ht _ _ _ => exact quotient_of_fitting_top ht
  | naturalDual _ _ ht _ => exact quotient_of_fitting_top ht
  | repeatedNatural _ _ _ _ _ ht _ => exact quotient_of_fitting_top ht

private theorem source_actor_cases {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (hL : IsQuasisimple (generalizedFitting D))
    (c : QuasisimpleSourceConclusion ρ (generalizedFitting D)) :
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

end ComponentRows

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)
include d

/-- The source actor cases preserve both the actual isomorphisms and the
Thompson equality in the quasisimple-actor branch. They assert no ambient equality. -/
theorem offender_actor_of_quasisimple_source
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup)) :
    (IsQuasisimple d.offenderGroup ∧
      (thompsonGroup H).map coreProjection = d.offenderGroup) ∨
      (∃ n, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (d.offenderGroup ≃* Equiv.Perm (Fin n))) ∨
      Nonempty (d.offenderGroup ≃* Atlas.G2.Model (ZMod 2)) := by
  rcases ComponentRows.source_actor_cases d.offenderAction
    (d.offender_fitting_quasisimple hL) c with h | h
  · exact Or.inl ⟨h, d.thompson_image_eq_quasisimple_offender h⟩
  · exact Or.inr h

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
