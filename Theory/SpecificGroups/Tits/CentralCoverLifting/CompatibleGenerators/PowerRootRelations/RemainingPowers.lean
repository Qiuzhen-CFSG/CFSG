module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingPowers.Arithmetic

/-!
# The two remaining normalized power equations

The literal source words `r₁²` and `s₃⁴` evaluate to one in
`NormalizedPresentation`. Additional central word identities, followed by
integer combinations with the ten defining correction equations, eliminate
their central errors. The replayable calculation is retained in
`RemainingPowers/source/certificate.json`; Lean checks every word rewrite and
integer combination.

Applying the four-seed reduction now leaves precisely `[s₁,s₃] = 1` and
`[s₁,s₆] = s₁ s₂ s₃²` as premises for all twenty seeds and all 23 power/root
relations. The commutator convention is `a⁻¹ b⁻¹ a b`.

Source: Parrott, “A Characterization of the Tits' Simple Group” (1972), §5,
p.683, as transcribed in `refs/original/n-group-global/parrott-tits-presentation.md`.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators

/-- The normalized lift of the source generator r₁ has square one. -/
theorem powerRoot_r1_square :
    FreeGroup.lift normalizedGenerator (parrottRelator .i_r1) = 1 :=
  (normalizedRelatorError_eq_one_iff .i_r1).mp
    PowerRootWords.RemainingPowers.r1_error_eq_one

/-- The normalized lift of the source generator s₃ has fourth power one. -/
theorem powerRoot_s3_fourth :
    FreeGroup.lift normalizedGenerator (parrottRelator .i_s3) = 1 :=
  (normalizedRelatorError_eq_one_iff .i_s3).mp
    PowerRootWords.RemainingPowers.s3_error_eq_one

/-- The two power equations discharge the power premises of the four-seed
reduction, leaving only the two independently owned commutator equations. -/
theorem powerRoot_seed_relations_of_commutators
    (h13 : FreeGroup.lift normalizedGenerator (parrottRelator .ii_s1_s3) = 1)
    (h16 : FreeGroup.lift normalizedGenerator (parrottRelator .iii_s1_s6) = 1) :
    ∀ j, isPowerRootSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 := by
  apply powerRoot_seed_relations_of_four
  intro j hj
  cases j <;> first
    | exact powerRoot_r1_square
    | exact powerRoot_s3_fourth
    | exact h13
    | exact h16
    | cases hj

/-- Recover the three omitted root equations from the same two commutator
premises, using the actual defining correction equations. -/
theorem powerRoot_relations_of_commutators
    (h13 : FreeGroup.lift normalizedGenerator (parrottRelator .ii_s1_s3) = 1)
    (h16 : FreeGroup.lift normalizedGenerator (parrottRelator .iii_s1_s6) = 1) :
    ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 :=
  powerRoot_relations_of_seed (powerRoot_seed_relations_of_commutators h13 h16)

end Tits.CentralCoverLifting.CompatibleGenerators
