module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Reductions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.SpecificGroups.Held.Automorphisms.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalSubgroups
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.Residual
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.IntervalNormalizer.Inner
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.LocalActions

/-!
# Full Held interval normalizers under irreducibility

If every inner two-group action on the odd complement is reducible, then
failure of PairReducible forces a genuinely outer actor preserving the pair.
The full-normalizer quotient bound and the inner interval calculation at S
then control the full Sylow normalizer. Frattini reduces the remaining
interval normalizers to their inner normalizers.

The conditional reductions remain available. The final theorem
`intervalNormalizer_of_local_placement` supplies both inner calculations
from the literal local subgroup proofs. Its only additional model premises
are full automorphism realization and the bound of two on the permutation
normalizer quotient. No global pair placement is required.
In particular hI is retained: the recorded GAP evidence for a reducible E₉
pair fails the unrestricted full-normalizer assertion at R2 = S.

Sources: Aschbacher–Smith, printed pp.509–511 and 747–748; GLS3, Table 5.3p.
The original source does not list this retained Held branch; the final theorem
establishes the additional local model calculation required by that branch.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs

/-- Failure of pair reducibility forces an outer pair actor once all inner
two-group actions are known to be reducible. No action catalogue is assumed. -/
theorem exists_outer_pair_actor_of_not_pairReducible
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (S R : Subgroup Held.He) (hI : ¬ PairReducible S R)
    (hinner : ∀ E : Subgroup (MulAut R), E ≤ (innerPairAction S R).range →
      IsPGroup 2 E → ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
        ∀ b ∈ E, ∀ x ∈ A, quotientAut (frattini R) b x ∈ A) :
    ∃ a : Held.LocalPairs.permutationPairStabilizer S R,
      a.val.val ∉ Held.permutationGroup := by
  have hnot : ¬ pairAutomizer S R ≤ (innerPairAction S R).range := by
    intro hle
    apply hI
    intro D hD htwo
    exact hinner D (hD.trans hle) htwo
  obtain ⟨a, _, hout⟩ := exists_outer_actor_of_not_le_inner hrealize S R
    (pairAutomizer S R) le_rfl hnot
  exact ⟨a, hout⟩

/-- Conditional assembly of the full interval normalizer from inner calculations.
The source-specific lower bound by O₂(O²(RS)) and the local placement are used
to establish hinnerNormalizer, rather than assumed to imply it here. -/
theorem intervalNormalizer_of_inner
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (S : Sylow 2 Held.He) (R R2 : Subgroup Held.He)
    (hI : ¬ PairReducible (S : Subgroup Held.He) R)
    (hself : normalizer (S : Set Held.He) = (S : Subgroup Held.He))
    (hinnerAction : ∀ E : Subgroup (MulAut R), E ≤ (innerPairAction S R).range →
      IsPGroup 2 E → ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
        ∀ b ∈ E, ∀ x ∈ A, quotientAut (frattini R) b x ∈ A)
    (hR2S : R2 ≤ S) (hindex : R2.relIndex S ≤ 2)
    (hinnerNormalizer : normalizer (R2 : Set Held.He) ≤
      normalizer (Held.LocalPairs.residual S R : Set Held.He)) :
    Held.LocalPairs.automorphismNormalizer R2 ≤
      Held.LocalPairs.automorphismNormalizer (Held.LocalPairs.residual S R) := by
  obtain ⟨a, hout⟩ := exists_outer_pair_actor_of_not_pairReducible hrealize S R hI hinnerAction
  exact Held.LocalPairs.PairCoverage.IntervalNormalizer.automorphismNormalizer_interval_le_of_outer_pair
    hrealize hbound S R R2 hself hR2S hindex hinnerNormalizer a hout

/-- Assemble the entire interval from its inner normalizers and inner-action
reducibility. Taking the inner calculation at S supplies the Sylow step;
the given lower bound places S in that same interval. Both concrete local
calculations are still premises to be supplied by the local model proofs. -/
theorem intervalNormalizer_of_inner_calculations
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (S : Sylow 2 Held.He) (R : Subgroup Held.He)
    (hI : ¬ PairReducible (S : Subgroup Held.He) R)
    (hinnerAction : ∀ E : Subgroup (MulAut R), E ≤ (innerPairAction S R).range →
      IsPGroup 2 E → ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
        ∀ b ∈ E, ∀ x ∈ A, quotientAut (frattini R) b x ∈ A)
    (hinnerNormalizers : ∀ U : Subgroup Held.He,
      Held.LocalPairs.twoCore S R ≤ U → U ≤ S → U.relIndex S ≤ 2 →
        normalizer (U : Set Held.He) ≤ normalizer (Held.LocalPairs.residual S R : Set Held.He))
    (R2 : Subgroup Held.He) (hQR2 : Held.LocalPairs.twoCore S R ≤ R2)
    (hR2S : R2 ≤ S) (hindex : R2.relIndex S ≤ 2) :
    Held.LocalPairs.automorphismNormalizer R2 ≤
      Held.LocalPairs.automorphismNormalizer (Held.LocalPairs.residual S R) := by
  obtain ⟨a, hout⟩ := exists_outer_pair_actor_of_not_pairReducible hrealize S R hI hinnerAction
  have hinnerS := hinnerNormalizers S (hQR2.trans hR2S) le_rfl (by simp)
  exact Held.LocalPairs.PairCoverage.IntervalNormalizer.automorphismNormalizer_interval_le_of_inner_and_outer_pair
    hrealize hbound S R R2 hR2S hindex hinnerS
      (hinnerNormalizers R2 hQR2 hR2S hindex) a hout

/-- Every full automorphism normalizer in the two-core interval preserves
the residual of a locally placed irreducible Held pair.

The literal local calculations discharge inner-action reducibility and all
inner normalizer inclusions. Irreducibility supplies an outer pair actor;
the quotient bound controls the full Sylow normalizer, and the Frattini
argument controls the remaining interval subgroups. The lower bound is
O₂(O²(RS)), while the subgroup normalized in the conclusion is O²(RS).
-/
theorem intervalNormalizer_of_local_placement
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ Held.LocalPairs.PairCoverage.localOvergroup i)
    (hI : ¬ PairReducible (S : Subgroup Held.He) R)
    (R2 : Subgroup Held.He) (hQR2 : Held.LocalPairs.twoCore S R ≤ R2)
    (hR2S : R2 ≤ S) (hindex : R2.relIndex S ≤ 2) :
    Held.LocalPairs.automorphismNormalizer R2 ≤
      Held.LocalPairs.automorphismNormalizer (Held.LocalPairs.residual S R) := by
  exact intervalNormalizer_of_inner_calculations hrealize hbound S R hI
    (fun E hE _ => LocalActions.inner_invariant_of_placement i S R h hplace E hE)
    (inner_intervalNormalizer i S R h hplace hI) R2 hQR2 hR2S hindex

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
