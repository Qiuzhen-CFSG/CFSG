module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.LocalConjugate.ZJFactorization
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.LocalConjugate.Quotient

/-!
# ZJ factorization for the canonical local subgroup

Apply the general factorization to the literal quotient-defined `M₂` and the
selected subgroup `R`. This supplies the factorization premise of
`action_exists_admissible_ZJ_conjugate_of_odd_factorization` in the parent
`LocalConjugate` module. The parent must establish the five local structural
premises below, as well as the odd-factor containment and involution membership
used in that conjugation step.

Source: GLS, Volume 4, Chapter 2, Lemma 7.11. This is the conditional ZJ step;
it does not assert that the canonical quotient has these structural properties.
-/

noncomputable section

namespace BenderSuzuki.ZD

/-- The ZJ step on the actual `M₂` of `(7F)`, with the prime and `R` from the
maximal-normalizer configuration. In particular the Sylow premise is in
`M₂ ⊔ R`, not in the final two-point stabilizer. -/
public theorem ActionMaximalNormalizerData.localM2_zj_factorization
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (q : ActionMaximalNormalizerData d beta)
    (hsolv : Group.IsSolvable ↥(actionLocalM2InG Z M q.chosen.Q ⊔ q.R))
    (hSylow : HasAbelianSylow 2 ↥(actionLocalM2InG Z M q.chosen.Q ⊔ q.R))
    (hR : theorem4bIsSylowSubgroupOf d.p q.R
      (actionLocalM2InG Z M q.chosen.Q ⊔ q.R))
    (hcore : pCore d.p ↥(actionLocalM2InG Z M q.chosen.Q ⊔ q.R) ≠ ⊥)
    (htheta : (pPrimeCore d.p ↥(actionLocalM2InG Z M q.chosen.Q ⊔ q.R)).map
        (actionLocalM2InG Z M q.chosen.Q ⊔ q.R).subtype =
      corollary64Theta d.p (actionLocalM2InG Z M q.chosen.Q)) :
    actionLocalM2InG Z M q.chosen.Q =
      corollary64Theta d.p (actionLocalM2InG Z M q.chosen.Q) ⊔
        (actionLocalM2InG Z M q.chosen.Q ⊓ Subgroup.normalizer
          (corollary64Z ⟨d.p, d.hp⟩ q.R : Set G)) := by
  exact local_zj_factorization d.hp d.hpOdd
    (actionLocalM2InG Z M q.chosen.Q) q.R hsolv hSylow hR hcore htheta

end BenderSuzuki.ZD
