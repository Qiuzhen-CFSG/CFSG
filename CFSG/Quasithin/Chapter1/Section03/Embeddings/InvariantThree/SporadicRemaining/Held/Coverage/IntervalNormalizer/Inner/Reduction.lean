module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Reductions
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Reduction

/-!
# Local inputs for the inner Held interval calculation

The source PairInput supplies oddness of R and simplicity of the actual
Held carrier. A commutator calculation on the local two-core can therefore
place that core in O₂(O²(RS)). An ambient normalizer containment and a
normalizer calculation in M/O₂(M) then put every required inner normalizer
in RS, which normalizes its relative residual.

Both model calculations remain explicit premises. These are conditional
assembly lemmas, not the completed Held interval-normalizer theorem. Its
irreducibility hypothesis may be used to discharge the local premises and
must be retained in the final source-theorem assembly.

Sources: Aschbacher–Smith, printed pp.509–511 and 747–748; GLS3, Table 5.3p.
-/

public section

open Subgroup
open Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.IntervalNormalizer
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs

/-- PairInput discharges oddness in the commutator-to-core reduction. -/
theorem localTwoCore_le_pair_twoCore_of_commutator
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i)
    (hcomm : ⁅localTwoCore i, R⁆ = localTwoCore i) :
    localTwoCore i ≤ Held.LocalPairs.twoCore S R := by
  apply localTwoCore_le_twoCore_of_commutator i S R hplace _ hcomm
  rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;> norm_num

/-- The two independent model calculations imply the requested inner inclusion.
Simplicity is inherited from PairInput; no separate simplicity certification
is required from the ambient normalizer calculation. -/
theorem inner_intervalNormalizer_of_local_calculations
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i)
    (hcore : localTwoCore i ≤ Held.LocalPairs.twoCore S R)
    (hambient : IsSimpleGroup Held.He → ∀ U : Subgroup Held.He,
      localTwoCore i ≤ U → U ≤ S → U.relIndex S ≤ 2 →
        normalizer (U : Set Held.He) ≤ localOvergroup i)
    (hquotient : ∀ U : Subgroup Held.He,
      Held.LocalPairs.twoCore S R ≤ U → U ≤ S → U.relIndex S ≤ 2 →
        normalizer (localImage i U : Set (LocalQuotient i)) ≤
          localImage i (R ⊔ (S : Subgroup Held.He)))
    (U : Subgroup Held.He) (hQU : Held.LocalPairs.twoCore S R ≤ U)
    (hUS : U ≤ S) (hindex : U.relIndex S ≤ 2) :
    normalizer (U : Set Held.He) ≤
      normalizer (Held.LocalPairs.residual S R : Set Held.He) := by
  apply le_trans _ (pairProduct_le_normalizer_residual S R)
  exact normalizer_le_pairProduct_of_localQuotient i S R U hplace hUS
    (hambient (simple_of_pairInput h) U (hcore.trans hQU) hUS hindex)
    (hquotient U hQU hUS hindex)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
