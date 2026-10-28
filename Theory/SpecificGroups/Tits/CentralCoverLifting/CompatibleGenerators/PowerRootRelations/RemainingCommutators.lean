module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Elimination

/-!
# The two remaining normalized Parrott commutators

Central word identities, followed by integer combinations with the defining
normalization equations, kill the errors of II(s₁,s₃) and III(s₁,s₆).
The calculation uses the literal `NormalizedPresentation`: the original
relators are central there, and are not assumed to vanish.

Applying `powerRoot_seed_relations_of_four` now leaves only the two power
equations `r₁² = 1` and `s₃⁴ = 1` explicit. Their unconditional proofs and the
final power/root assembly belong to the separate power calculation.

Source: Parrott (1972), §5, p.683; the convention is `[a,b] = a⁻¹ b⁻¹ a b`,
and the right side of III(s₁,s₆) is the actual word `s₁ s₂ s₃²`.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators

/-- Source II(s₁,s₃) holds without any additional relation hypotheses. -/
theorem powerRoot_s1_s3_commutator :
    FreeGroup.lift normalizedGenerator (parrottRelator .ii_s1_s3) = 1 :=
  (normalizedRelatorError_eq_one_iff .ii_s1_s3).mp
    PowerRootWords.remainingCommutator_error11_eq_one

/-- Source III(s₁,s₆), including its prescribed right side, holds unconditionally. -/
theorem powerRoot_s1_s6_commutator :
    FreeGroup.lift normalizedGenerator (parrottRelator .iii_s1_s6) = 1 :=
  (normalizedRelatorError_eq_one_iff .iii_s1_s6).mp
    PowerRootWords.remainingCommutator_error13_eq_one

/-- The four-seed reduction now requires only its two power equations. -/
theorem powerRoot_seed_relations_of_two_powers
    (hr1 : FreeGroup.lift normalizedGenerator (parrottRelator .i_r1) = 1)
    (hs3 : FreeGroup.lift normalizedGenerator (parrottRelator .i_s3) = 1) :
    ∀ j, isPowerRootSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 := by
  apply powerRoot_seed_relations_of_four
  intro j hj
  cases j <;> first
    | exact hr1
    | exact hs3
    | exact powerRoot_s1_s3_commutator
    | exact powerRoot_s1_s6_commutator
    | cases hj

/-- The same two powers suffice for all 23 original equations in groups I–V. -/
theorem powerRoot_relations_of_two_powers
    (hr1 : FreeGroup.lift normalizedGenerator (parrottRelator .i_r1) = 1)
    (hs3 : FreeGroup.lift normalizedGenerator (parrottRelator .i_s3) = 1) :
    ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 :=
  powerRoot_relations_of_seed (powerRoot_seed_relations_of_two_powers hr1 hs3)

end Tits.CentralCoverLifting.CompatibleGenerators
