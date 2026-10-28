module
public import Theory.SpecificGroups.Alternating.FiveChiefDegree
public import Mathlib.GroupTheory.IsPerfect
public import Theory.ElementaryAbelian.Basic

/-!
# A₅ extensions act trivially on small elementary binary groups

A nontrivial action of a two-perfect A₅ extension on a two-group requires at
least sixteen elements. Perfectness supplies two-perfection, so an elementary
binary group of order at most eight is fixed. The actual J₄ placement applies
this to a minimal invariant subgroup from the pure involution catalogue.

Source application: Aschbacher--Smith A.3.12(17), printed pp.47--48.
-/

public section
open Subgroup
namespace Theory.GroupTheory.AlternatingFiveSmallAction

/-- A perfect group with two-core quotient A5 acts trivially on an elementary
binary group of order at most eight. -/
theorem small_elementary_action_trivial {B A : Type*} [Group B] [Finite B]
    [Group.IsPerfect B] [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hA : Nat.card A ≤ 8) (f : B →* MulAut A) : f = 1 := by
  have hp : IsPPerfect 2 B := by
    intro N hN hquot
    let := hN
    have hs : Subsingleton (B ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (B ⧸ N) hquot.isNilpotent
    apply eq_top_iff.mpr
    intro b _
    exact (QuotientGroup.eq_one_iff b).mp (Subsingleton.elim _ _)
  by_contra hf
  have hh := alternatingGroup.FiveChiefDegree.sixteen_le_card_of_nontrivial_action
    hp eB f hf (IsElementaryAbelian.isPGroup 2 A)
  omega

end Theory.GroupTheory.AlternatingFiveSmallAction
