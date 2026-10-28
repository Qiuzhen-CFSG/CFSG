module

public import Theory.Mathieu.M12.Properties.SylowFixedActions
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Stellmacher.SectionsOneToFourDefs

/-!
# The M₁₂ component fixed-action obstruction

The component in both F.6.18(12) and (13) is the actual Witt-design M₁₂. A
faithful four-group action fixing one of its Sylow two-subgroups pointwise is
impossible: the intrinsic pointwise-stabilizer calculation bounds the actor
order by two. Thus the requested fixed-subgroup obstruction follows already
from faithfulness, order four and pointwise fixation.

The conditional export retains the automorphism Sylow omega-center premise
supplied by `SingleOvergroup.AutM12Center`. The stronger intrinsic bound makes
that premise unnecessary here. In particular, this proof needs neither an
assumed index-two comparison nor an outer-automorphism classification.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.18(12)–(13), printed pp.309–310, and the component
paragraph of 15.4.18, printed pp.1162–1163. The parent owns the model application
and quotient transport, including the Aut(M₁₂) alternative.
-/

open Subgroup
open Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels

/-- There is no faithful action of a group of order four on M₁₂ fixing a
Sylow two-subgroup pointwise. -/
public theorem mathieuTwelve_no_faithful_sylow_fixed_action
    {A : Type*} [Group A] (P : Sylow 2 M12) (hA : Nat.card A = 4)
    (ρ : A →* MulAut M12) (hfixed : ∀ a : A, ∀ x : P, ρ a x = x) :
    ¬ Function.Injective ρ := by
  intro hinj
  have hbound := m12_faithful_sylow_fixed_action_card_le_two P ρ hinj hfixed
  omega

/-- The intrinsic M₁₂ obstruction in the conditional interface used by the
component branch. The center premise is redundant by the stronger rigidity
theorem; the two-core and its centralizer are internal to the fixed subgroup. -/
public theorem mathieuTwelve_fixed_action_obstruction
    (_hcenter : ∀ Q : Sylow 2 (MulAut M12),
      Nat.card (Stellmacher.omegaOneCenterAmbient (Q : Subgroup (MulAut M12))) = 2)
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (P : Sylow 2 M12) (hA : Nat.card A = 4)
    (ρ : A →* MulAut M12) (hinj : Function.Injective ρ)
    (hfixed : ∀ a : A, ∀ x : P, ρ a x = x) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup := by
  exact (mathieuTwelve_no_faithful_sylow_fixed_action P hA ρ hfixed hinj).elim

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels
