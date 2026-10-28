module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Spin
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.SpinActions.Consequences

/-!
# Parker spin generator formulas and the orthogonal direct sum

`SpinActions.spinRestriction` is restriction of the actual spin orbit functions
to the two axes. It is a linear equivalence `SpinSpace ≃ₗ[ℝ] B1A2 × B1A3`, and
`spinRestriction_isometry` identifies the normalized form with the sum form.

`B3A2` uses the actual `k3` orbits on axis 2 and the actual `z3` sign change.
`SpinActions.B3Axis2` supplies its dimension 2048, signed vectors, orthonormal
basis, positive form, induced monomial actions, and geometric kernel criterion.

The `psi1B1_delta`, `psi2B1_delta`, `psiAut2Even_delta`, `psiAut2Odd_delta`,
and `psiAut1Odd_delta` formulas prove the actions in Lemma 27.3(1)–(4).
The odd maps have distinct targets: `psiAut2Odd` maps to `B3A2`, while
`psiAut1Odd` maps to `B1A3`. Their normalization and loop-automorphism facts
are proved from `IsStandard`, and the point maps are the published permutations.
The `induced_psi*` theorems identify the maps with normalized ambient restrictions.

`kernel_generators_B1` and `kernel_generators_B3` give the concrete generator
effects in (5)–(6), without asserting an entire subgroup-kernel equality.
The parent construction owns that identification and the final signed-module
assembly; its triality structure supplies the ambient normalization hypotheses.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.3 and the spin-space construction,
printed pp. 146–147 (PDF p. 79).
-/
