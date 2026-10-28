module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.CentralizerOrders
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Exceptional

/-!
# Exclusion of the original proper linear residual subgroup

The original minimal simple context gives the local embedding, two-core
growth, nontrivial centralizer core, odd supplement and normalizer count.
The proper-core branch forces the centralizer normal closure to be O₂(M).
The exceptional equality branch then gives a forbidden square root.
All source premises of GLS IV, Chapter 2, Proposition 15.1 are discharged.
-/

namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory
universe u

/-- The original proper linear source context is impossible. -/
public theorem LinearExclusion.Context.false
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    {z t : G} {n : ℕ} (d : LinearExclusion.Context Z M z t n) : False :=
  d.exceptionalCore_false d.centralizer_orders.1 d.centralizer_orders.2
    d.centralizerClosure_eq_twoCore

/-- GLS IV, Chapter 2, Proposition 15.1 with its original source hypotheses. -/
public theorem proper_residualGenerated_linear_false
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (n : ℕ) (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n) : False :=
  LinearExclusion.Context.false ⟨h, r, ha, hz, hzM, ht, htM, hL, heven, hn, e⟩

end BenderSuzuki.ZD
