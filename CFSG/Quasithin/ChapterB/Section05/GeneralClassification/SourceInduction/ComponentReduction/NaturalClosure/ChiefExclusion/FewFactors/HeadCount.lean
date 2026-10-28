module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors.HeadCount.MovedQuotients
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors.HeadCount.FlagBound
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors.SmallDegree
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.Flags

/-!
# From bounded multiplicities to triviality of the second head action

The actual second component acts linearly on dual multiplicity spaces over
finite endomorphism fields of characteristic two. Its established
small-degree obstruction kills each such action in dimension at most two.
The quotient maps to all simple L-modules then put each displacement in
the actual L-module radical, proving triviality on the literal head.

The flag adapter uses perfectness to exclude central simple quotients of
W = [V,L]. The final theorem discharges its dimension premise using the
original chief flag comparison proved in `HeadCount.FlagBound`.
The count is exactly `InvariantChiefFlag.noncentral`, hence the literal
`CentralFactors.noncentralFactors`, including zero, one and two factors.
Neither construction of a flag nor the cross action is used here.

Source: Aschbacher–Smith, B.5.9, printed p.108, the c = 2 centralizer
argument (1 March 2004 manuscript).
-/

@[expose] public section

open Representation
open scoped MonoidAlgebra
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors
namespace HeadCount
set_option backward.isDefEq.respectTransparency false

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The genuine second component is trivial on the head when all dual multiplicities are at most two. -/
theorem secondHead_eq_one_of_dualMultiplicity_le_two [Module.Finite (ZMod 2) V]
    {A L : Subgroup G} (hL : Theory.GroupTheory.IsComponent G L)
    (d : SecondComponent ρ A L)
    (h : ∀ N : Subrepresentation (componentAction ρ L), IsCoatom N →
      Module.finrank (Module.End (ZMod 2)[L] N.quotientRepresentation.asModule)
        (DualMultiplicity (componentAction ρ L) N.quotientRepresentation) ≤ 2) :
    secondHead ρ hL d = 1 := by
  apply head_action_eq_one_of_dualAction_eq_one
  intro N hN
  let : IsIrreducible N.quotientRepresentation :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
  exact seed_small_degree ρ d.seed d.isComponent
    (dualAction (componentAction ρ L) (secondAction ρ hL d)
      (moved_commute ρ hL d) N.quotientRepresentation) (h N hN)


/-- The literal flag bound supplies the small-degree premise for every noncentral simple quotient.
The final theorem below discharges this comparison using the original chief flag. -/
theorem secondHead_eq_one_of_flag_multiplicity_bound [Module.Finite (ZMod 2) V]
    {A L : Subgroup G} (hL : Theory.GroupTheory.IsComponent G L)
    (d : SecondComponent ρ A L) (f : InvariantChiefFlag ρ A L ⊤)
    (hcount : f.noncentral.card ≤ 2)
    (hbound : ∀ N : Subrepresentation (componentAction ρ L), IsCoatom N →
      N.quotientRepresentation ≠ 1 →
      Module.finrank (Module.End (ZMod 2)[L] N.quotientRepresentation.asModule)
        (DualMultiplicity (componentAction ρ L) N.quotientRepresentation) ≤
          f.noncentral.card) : secondHead ρ hL d = 1 := by
  apply secondHead_eq_one_of_dualMultiplicity_le_two ρ hL d
  intro N hN
  exact (hbound N hN (moved_coatom_quotient_ne_one ρ hL N hN)).trans hcount

/-- At most two literal noncentral chief factors force the actual second head action to be trivial.
This includes counts zero and one and uses neither stability of the flag under the second
component nor its cross action. It is the head-triviality input to the separate centralizer
exclusion in B.5.9. -/
theorem secondHead_eq_one_of_noncentral_card_le_two [Finite G] [Module.Finite (ZMod 2) V]
    {A L : Subgroup G} (hL : Theory.GroupTheory.IsComponent G L)
    (d : SecondComponent ρ A L) (f : InvariantChiefFlag ρ A L ⊤)
    (hcount : f.noncentral.card ≤ 2) : secondHead ρ hL d = 1 := by
  apply secondHead_eq_one_of_flag_multiplicity_bound ρ hL d f hcount
  intro N hN _
  exact moved_coatom_dualMultiplicity_finrank_le_noncentral ρ f hL N hN

end HeadCount
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors
