module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.Setup

/-!
# The commutator kernel in the proper-core branch

GLS, Volume 4, Chapter 2, Lemma 15.7 constructs `R₀ = [R₁,K]`,
where `K = D ∩ L`. Here the first argument is the actual normal closure
`R = ⟨Jᴹ⟩`. Any use of the source normalizer `R₁` must first identify it
with this `R`. This definition does not assert homocyclicity or normality
of `R₀`; those are conclusions of the local analysis.

The elementary containment `[R,K] ≤ R ≤ O₂(M)` follows because `R` is
normal in `M`. All the subgroups in this construction are internal to `M`.
Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 15.6–15.7.
-/

noncomputable section

namespace BenderSuzuki.ZD

/-- The source candidate `R₀ = [R,K]` inside `M`, with `K = D ∩ L`. -/
@[expose] public def linearCommutatorKernel
    {G : Type*} [Group G] (M : Subgroup G) (z t : G) : Subgroup M :=
  ⁅linearCentralizerClosure M z t,
    (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M⁆

/-- The commutator kernel is contained in the normal closure. -/
public theorem linearCommutatorKernel_le_closure
    {G : Type*} [Group G] {M : Subgroup G} {z t : G} :
    linearCommutatorKernel M z t ≤ linearCentralizerClosure M z t := by
  let : (linearCentralizerClosure M z t).Normal := by
    unfold linearCentralizerClosure
    infer_instance
  exact Subgroup.commutator_le_left _ _

/-- The given closure order places the commutator kernel in the two-core. -/
public theorem linearCommutatorKernel_le_twoCore
    {G : Type*} [Group G] {M : Subgroup G} {z t : G} {n : ℕ}
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2) :
    linearCommutatorKernel M z t ≤ pCore 2 M :=
  linearCommutatorKernel_le_closure.trans (linearCentralizerClosure_le_twoCore hR)

end BenderSuzuki.ZD
