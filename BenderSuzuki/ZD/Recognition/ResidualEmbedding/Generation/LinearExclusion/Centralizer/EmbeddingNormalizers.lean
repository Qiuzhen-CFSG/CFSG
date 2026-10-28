module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.EmbeddingNormalizers.NormalizerControl
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.EmbeddingNormalizers.OddNormalizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.EmbeddingNormalizers.RegularityContracts

/-!
# Linear centralizer embedding and normalizer control

Normalizer control for every nontrivial subgroup of J=C_G(L) is proved from
the original Context. The proof retains the unitary normalizer-circle case
until its actual coset degree forces transitivity and contradicts faithfulness.

For the embedding, the fixed-coset and moved-coset action is established,
including |Γᵤ|=|L| and faithfulness of J. The applications below construct
the actual homomorphism J →* L and its marked PSL₂ composite from freeness
of L on Γᵤ. That freeness, via Proposition 12.13 and the prime-stabilizer
argument, remains an explicit earlier-source premise. Thus this module does
not yet assert the unconditional CentralizerLocalModelData theorem.

Source: GLS IV, Chapter 2, Lemmas 12.12–12.14 and 15.2(a,c),
refs/KGroup/GLS4/Chapter2.tex.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup PFAppendixIII
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

/-- The actual embedding from Lemma 12.14(a), with its freeness premise
still explicit and its regularity and faithfulness premises discharged. -/
public theorem Context.centralizer_embedding_of_movedPointFree
    (hfree : ∀ u ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution u →
      ∀ x : residualGenerated M z t, ∀ beta : G ⧸ M,
        u • beta ≠ beta → (x : G) • beta = beta → x = 1) :
    ∃ f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t,
      Function.Injective f := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card'
    (G := residualPairStabilizer M t) 2 d.even_pair.two_dvd
  have hui : PFAppendixIII.IsInvolution (u : G) := IsInvolution.map_of_injective
    (orderOf_eq_prime_iff.mp hu).symm (residualPairStabilizer M t).subtype
    Subtype.val_injective
  exact d.centralizer_embedding_of_regular u.property hui
    (fun _ _ ha hb => d.regular_on_moved_of_free u.property hui
      (hfree u u.property hui) ha hb)

/-- Connect the constructed embedding and the full source normalizer theorem
to the interface consumed by the independent two-core and counting arguments.
The source freeness theorem must still be supplied in final assembly. -/
public theorem Context.centralizerLocalModelData_of_movedPointFree
    (hfree : ∀ u ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution u →
      ∀ x : residualGenerated M z t, ∀ beta : G ⧸ M,
        u • beta ≠ beta → (x : G) • beta = beta → x = 1) :
    Nonempty (CentralizerLocalModelData d) := by
  obtain ⟨f, hf⟩ := d.centralizer_embedding_of_movedPointFree hfree
  exact ⟨⟨f, hf, d.normalizer_control_of_le_centralizer⟩⟩

/-- The homomorphism is marked by the original PSL₂ isomorphism; the
composite remains injective into that actual matrix-group carrier. -/
public theorem Context.marked_centralizer_embedding_of_movedPointFree
    (hfree : ∀ u ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution u →
      ∀ x : residualGenerated M z t, ∀ beta : G ⧸ M,
        u • beta ≠ beta → (x : G) • beta = beta → x = 1) :
    ∃ f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t,
      Function.Injective f ∧ Function.Injective (d.model.toMonoidHom.comp f) := by
  obtain ⟨f, hf⟩ := d.centralizer_embedding_of_movedPointFree hfree
  exact ⟨f, hf, d.model.injective.comp hf⟩

end BenderSuzuki.ZD.LinearExclusion
