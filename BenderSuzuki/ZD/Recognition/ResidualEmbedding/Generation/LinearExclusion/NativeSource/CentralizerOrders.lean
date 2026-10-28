module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.TwoStructure
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCount
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.NativeSource

/-!
# Source centralizer orders and reduction to the equality case

The original source context supplies all two-structure hypotheses of the
normalizer count. Hence J has order two and its literal M-normal closure
has order 2q². The completed proper-core argument then identifies this
normal closure with O₂(M), leaving the exceptional equality branch of 15.7.

Source: GLS IV, Chapter 2, Lemmas 15.6–15.7.
-/

namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

/-- The full original source orders, without model or growth certificates. -/
public theorem Context.centralizer_orders :
    Nat.card (centralizer (residualGenerated M z t : Set G)) = 2 ∧
      Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2 :=
  d.centralizer_counts_of_localTwoData d.centralizerLocalTwoData

/-- The proper-core branch is impossible for the original source context. -/
public theorem Context.centralizerClosure_eq_twoCore :
    linearCentralizerClosure M z t = pCore 2 M :=
  d.centralizerClosure_eq_twoCore_of_orders d.centralizer_orders.1 d.centralizer_orders.2

end BenderSuzuki.ZD.LinearExclusion
