module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.EmbeddingNormalizers
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Freeness.TorusFixedPoints
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Freeness.PrimeStabilizers

/-!
# The actual linear centralizer embedding

The source split torus fixes exactly the two marked cosets. For the
remaining prime-order stabilizers, the concrete PSL₂ torus reflections
and odd-normalizer theorem exclude a fixed point moved by an involution
of the pair stabilizer. Thus L acts freely, and hence regularly, on the
moved cosets. Inverse evaluation embeds its centralizer J into L.

The final application constructs the original `CentralizerLocalModelData`:
the embedding and normalizer control are both proved from `Context`, with
no additional action, torus or recognition premise.

Source: GLS IV, Chapter 2, Proposition 12.13, Lemma 12.14 and
Lemma 15.2(a,c), `refs/KGroup/GLS4/Chapter2.tex`.
-/

namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

/-- Every stabilizer in L of a coset moved by a pair-stabilizer involution is trivial. -/
public theorem Context.movedPoint_free {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (x : residualGenerated M z t) (beta : G ⧸ M)
    (hbeta : u • beta ≠ beta) (hfix : (x : G) • beta = beta) : x = 1 :=
  d.movedPoint_free_of_torus_semiregular d.torus_semiregular huD hu x beta hbeta hfix

/-- Lemma 12.14(a) for the literal quotient action and original linear model. -/
public theorem Context.regular_on_moved {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    {a b : G ⧸ M} (ha : u • a ≠ a) (hb : u • b ≠ b) :
    ∃! x : residualGenerated M z t, (x : G) • a = b :=
  d.regular_on_moved_of_free huD hu (d.movedPoint_free huD hu) ha hb

/-- Lemma 12.14(b): inverse evaluation gives the actual centralizer embedding. -/
public theorem Context.centralizer_embedding :
    ∃ f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t,
      Function.Injective f :=
  d.centralizer_embedding_of_movedPointFree (fun _ huD hu => d.movedPoint_free huD hu)

/-- The embedding retains the actual matrix model already marked in the Context. -/
public theorem Context.marked_centralizer_embedding :
    ∃ f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t,
      Function.Injective f ∧ Function.Injective (d.model.toMonoidHom.comp f) :=
  d.marked_centralizer_embedding_of_movedPointFree
    (fun _ huD hu => d.movedPoint_free huD hu)

/-- Construct the full source 15.2(a,c) input for the independent two-core and counting arguments. -/
public theorem Context.centralizerLocalModelData : Nonempty (CentralizerLocalModelData d) :=
  d.centralizerLocalModelData_of_movedPointFree
    (fun _ huD hu => d.movedPoint_free huD hu)

end BenderSuzuki.ZD.LinearExclusion
