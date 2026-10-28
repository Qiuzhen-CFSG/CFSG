module

public import Theory.GroupAction.FourGroupOddCenter
public import Theory.GroupTheory.Covering

/-!
# The odd-center alternatives in the component branch

Notation A.3.5, printed p.43, defines Â₆ and Â₇ as quasisimple groups with
center of order three and central quotients A₆ and A₇. These are the covers
in F.6.18(6)–(9), printed pp.309–310; they are not double covers.

Every four-group action on such a component has a nonidentity actor with a
fixed nonidentity central element. Its fixed subgroup cannot have
self-centralizing two-core. The argument also applies when this component
lies in a covered symmetric extension: the action here is on the actual
component, whose center has order three, rather than on the whole extension.
Likewise, nontrivial odd centers in the special linear or unitary alternatives
are handled by the imported general theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, 15.4.18, printed pp.1162–1163. The parent supplies the
component and its action and applies these intrinsic obstructions.
-/

open Subgroup
open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels

/-- The center in the source triple-cover notation already excludes the
required fixed-subgroup configuration. -/
public theorem center_three_fixed_action_obstruction
    {A K : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group K] [Finite K] (hZ : Nat.card (center K) = 3)
    (hA : Nat.card A = 4) (ρ : A →* MulAut K) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup := by
  apply Theory.GroupAction.exists_fixedSubgroup_not_selfCentralizing_twoCore_of_odd_center
    (by rw [hZ]; decide) ?_ hA ρ
  intro hbot
  rw [hbot, Subgroup.card_bot] at hZ
  omega

/-- For an actual covering map onto a simple group, a kernel of order three
is the whole center. Thus this includes the source covers of A₆ and A₇. -/
public theorem triple_cover_fixed_action_obstruction
    {A K S : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group K] [Finite K] [IsQuasisimple K]
    [Group S] [Finite S] [IsQuasisimple S] [IsSimpleGroup S]
    (π : Covering K S) (hker : Nat.card π.toMonoidHom.ker = 3)
    (hA : Nat.card A = 4) (ρ : A →* MulAut K) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup := by
  apply center_three_fixed_action_obstruction (hA := hA) (ρ := ρ)
  rwa [← π.ker_eq_center_of_isSimple]

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels
