module

public import Theory.SpecificGroups.AlternatingSix.TwoCoverInvolutions
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.ResidualA4.ModelFacts

/-!
# The A₆ central-cover obstruction in the S₆ branch

Trivial odd core makes the component center a two-group. Schur's multiplier
bound and involution-lift calculation then show that a noncentral involution
forces this center to be trivial. This supplies the full universe-polymorphic
`SixCoverRigidity` contract; the source consumer supplies the actual central
quotient isomorphism and marked involution.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927; GLS3,
Theorem 5.2.3 and Proposition 5.2.4(a).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
open Subgroup Theory.GroupTheory
universe u

/-- The marked noncentral involution excludes every nontrivial A₆ cover
with trivial odd core. -/
theorem sixCoverRigidity : SixCoverRigidity.{u} := by
  intro Q _ _ _ hodd e hx
  apply AlternatingSix.TwoCoverInvolutions.center_eq_bot_of_noncentral_involution
    (e := e) (hx := hx)
  rw [IsQuasisimple.center_eq_pCore hodd]
  exact pCore_isPGroup

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
