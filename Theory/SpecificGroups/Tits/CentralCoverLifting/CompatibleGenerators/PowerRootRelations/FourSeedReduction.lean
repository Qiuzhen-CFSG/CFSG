module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.LinearReduction2
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.NormalizedPresentation

/-!
# Four remaining equations suffice for the normalized power/root relations

Checked central word identities and the ten normalization equations reduce all
23 equations in source groups I–V to two power and two commutator equations.
The four equations remain explicit premises here. In particular, this module
does not assert the missing unconditional `powerRoot_seed_relations` theorem.

Source: Parrott (1972), §5, p.683. All commutators are `a⁻¹ b⁻¹ a b`.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators
open PowerRootWords

/-- The four source equations still required by this reduction. -/
@[expose] def isRemainingPowerRootSeed : ParrottRelatorIndex → Bool
  | .i_r1 | .i_s3 | .ii_s1_s3 | .iii_s1_s6 => true
  | _ => false

/-- The checked word identities reduce the twenty seeds to four source equations. -/
theorem powerRoot_seed_relations_of_four
    (h : ∀ j, isRemainingPowerRootSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    ∀ j, isPowerRootSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 := by
  have h0 := (normalizedRelatorError_eq_one_iff .i_r1).mpr (h .i_r1 rfl)
  have h7 := (normalizedRelatorError_eq_one_iff .i_s3).mpr (h .i_s3 rfl)
  have h11 := (normalizedRelatorError_eq_one_iff .ii_s1_s3).mpr (h .ii_s1_s3 rfl)
  have h13 := (normalizedRelatorError_eq_one_iff .iii_s1_s6).mpr (h .iii_s1_s6 rfl)
  intro j hj
  apply (normalizedRelatorError_eq_one_iff j).mp
  cases j
  · exact h0
  · exact error1_of_four h0 h7 h13
  · exact error2_of_four h0
  · exact error3_of_four h0 h7 h13
  · exact error4_of_four h0 h7 h11 h13
  · exact error5_of_four h0 h7 h11 h13
  · exact error6_of_four h0 h7 h13
  · exact h7
  · exact error8_of_four h0 h7 h11 h13
  · exact error9_of_four h0 h7 h11 h13
  · exact error10_of_four
  · exact h11
  · exact error12_of_four h0 h7 h11 h13
  · exact h13
  · exact error14_of_four h0 h7 h11 h13
  · exact error15_of_four h0 h7 h11 h13
  · exact error16_of_four
  · exact error17_of_four
  · exact error18_of_four
  · exact error19_of_four h0 h7 h11 h13
  · exact error20_of_four h0 h7 h11 h13
  · exact error21_of_four h0 h7 h11 h13
  · exact error22_of_four h0 h7 h11 h13
  · cases hj
  · cases hj
  · cases hj
  · cases hj
  · cases hj
  · cases hj
  · cases hj
  · cases hj
  · cases hj
  · cases hj
  · cases hj
  · cases hj
  · cases hj
  · cases hj

/-- Application of the existing three-equation recovery to the four remaining seeds. -/
theorem powerRoot_relations_of_four
    (h : ∀ j, isRemainingPowerRootSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 :=
  powerRoot_relations_of_seed (powerRoot_seed_relations_of_four h)

end Tits.CentralCoverLifting.CompatibleGenerators
