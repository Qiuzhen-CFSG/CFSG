module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Basic

/-!
# The normal closure used in the linear complement argument

In GLS, Volume 4, Chapter 2, Lemmas 15.6–15.7, `J = C_G(L)` has order
two and its normal closure in `M` has order `2q²`. We use precisely that
normal closure, inside `M`, without identifying it in advance with the
normalizer called `R₁` during the source proof. Its given order makes it a
normal two-subgroup, hence a subgroup of `O₂(M)`.

The proper-containment and equality cases still require the local analysis
of Lemma 15.7. Neither its homocyclic subgroup nor its exceptional quotient
identifications are encoded as hypotheses of a purported source theorem here.
-/

noncomputable section

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII PFchapter1section1

/-- The actual normal closure of the centralizer, taken relative to `M`. -/
@[expose] public def linearCentralizerClosure
    {G : Type*} [Group G] (M : Subgroup G) (z t : G) : Subgroup M :=
  Subgroup.normalClosure
    ((Subgroup.centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M)

/-- The cardinality from Lemma 15.6 places its normal closure in `O₂(M)`.
This uses the two-core, not the two-residual or the odd core. -/
public theorem linearCentralizerClosure_le_twoCore
    {G : Type*} [Group G] {M : Subgroup G} {z t : G} {n : ℕ}
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2) :
    linearCentralizerClosure M z t ≤ pCore 2 M := by
  have hp : IsPGroup 2 (linearCentralizerClosure M z t) := by
    apply IsPGroup.of_card (n := n * 2 + 1)
    rw [hR, pow_add, pow_mul, pow_one, Nat.mul_comm]
  have hnormal : (linearCentralizerClosure M z t).Normal := by
    unfold linearCentralizerClosure
    infer_instance
  exact le_sSup ⟨hnormal, hp⟩

/-- The order of the centralizer is unchanged by viewing it inside `M`:
centralizing `L` forces membership in the actual two-point stabilizer. -/
public theorem linearCentralizer_subgroupOf_card
    {G : Type*} [Group G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) {z t : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (hJ : Nat.card (Subgroup.centralizer (residualGenerated M z t : Set G)) = 2) :
    Nat.card ((Subgroup.centralizer (residualGenerated M z t : Set G)).subgroupOf M) = 2 := by
  have hJM : Subgroup.centralizer (residualGenerated M z t : Set G) ≤ M :=
    (centralizer_residualGenerated_le_pair h hz hzM).trans inf_le_left
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJM).toEquiv).trans hJ

/-- The distinguished centralizer lies in the two-core once its normal
closure has the source order. No ambient normality is asserted. -/
public theorem linearCentralizer_subgroupOf_le_twoCore
    {G : Type*} [Group G] {M : Subgroup G} {z t : G} {n : ℕ}
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2) :
    (Subgroup.centralizer (residualGenerated M z t : Set G)).subgroupOf M ≤ pCore 2 M := by
  exact (Subgroup.subset_normalClosure).trans (linearCentralizerClosure_le_twoCore hR)

end BenderSuzuki.ZD
