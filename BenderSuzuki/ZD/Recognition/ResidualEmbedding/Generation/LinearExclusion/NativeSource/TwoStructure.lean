module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.CoreNontrivial
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.OddSupplement

/-!
# The original source two-structure in the proper linear case

Lemmas 15.3 and 15.4 give O₂(J)≠1. The Borel embedding, source normalizer
control and Burnside transfer then prove the actual odd supplement of 15.5.
This discharges every earlier-source input of the local two-structure used
by Lemma 15.6, with the original marked PSL₂ model and minimal simple setup.

Source: GLS IV, Chapter 2, Lemmas 15.3–15.5.
-/

namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

/-- All local two-structure fields follow from the original source context. -/
public theorem Context.centralizerLocalTwoData : CentralizerLocalTwoData d :=
  d.centralizerLocalTwoData_of_twoCore_ne_bot d.centralizer_twoCore_ne_bot

/-- The source carrier equality C₀=VY, with the actual odd cyclic Y≤J. -/
public theorem Context.centralizer_odd_supplement_source :
    ∃ Y : Subgroup G, Y ≤ centralizer (residualGenerated M z t : Set G) ∧
      Odd (Nat.card Y) ∧ IsCyclic Y ∧ Nat.card Y ∣ 2 ^ n - 1 ∧
      ((M ⊓ centralizer (closure (Z ∩ (M : Set G)) : Set G) : Subgroup G) : Set G) =
        ((pCore 2 M).map M.subtype : Set G) * (Y : Set G) :=
  d.centralizer_odd_supplement d.centralizer_twoCore_ne_bot

end BenderSuzuki.ZD.LinearExclusion
