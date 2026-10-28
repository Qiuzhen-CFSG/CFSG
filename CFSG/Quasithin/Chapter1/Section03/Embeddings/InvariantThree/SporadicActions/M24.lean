module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalOvergroups
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.SylowNormalizer

/-!
# Assembly of the M₂₄ Sylow-pair exclusion

Every source pair on the fixed Witt-design carrier is either already reducible
or lies in a local extension with two-group kernel and quotient S₃ × L₃(2).
In the latter case the quotient's normal three-subgroup lifts to a proper
nonzero subgroup of the Frattini quotient. The proved innerness of M₂₄
automorphisms and self-normalizing Sylow two-subgroups ensure invariance under
every actual pair automorphism.

`m24_carrierPairExclusion` assembles these proved inputs with no additional
premises. The earlier conditional reduction using universal local placement
is preserved separately; that stronger placement assertion is unnecessary.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528 of
`refs/quasithin.pdf`); GLS3, Table 5.3e.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions

/-- The local-extension and Sylow-normalizer calculations suffice for the
fixed-carrier exclusion; the quotient's invariant line is constructed. -/
theorem m24_carrierPairExclusion_of_local_overgroups
    (hloc : M24PairAction.LocalOvergroups)
    (hnorm : M24PairAction.SylowNormalizerControl) :
    CarrierPairExclusion ClassificationModels.SporadicName.m24.Carrier := by
  intro _ _ _ S R h
  obtain ⟨H, hSH, hRH, f, _, hker⟩ := hloc S R h
  exact M24PairAction.pairReducible_of_local_quotient S.toSubgroup R h.oddComplement
    H hRH ((hnorm S).trans hSH) f hker

/-- Every two-subgroup of the actual M₂₄ pair automizer preserves a proper
nonzero subgroup of the odd complement's Frattini quotient. -/
theorem m24_carrierPairExclusion :
    CarrierPairExclusion ClassificationModels.SporadicName.m24.Carrier := by
  intro _ _ _ S R h
  rcases M24PairAction.reducible_or_local_overgroup h with hred | ⟨H, hSH, hRH, f, _, hker⟩
  · exact hred
  · exact M24PairAction.pairReducible_of_local_quotient S.toSubgroup R h.oddComplement
      H hRH ((M24PairAction.sylowNormalizerControl S).trans hSH) f hker

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
