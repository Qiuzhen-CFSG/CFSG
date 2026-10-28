module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Setup
public import Theory.GroupTheory.InvolutoryExtension
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Generators
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Marking

/-!
# Assembling the long local subgroup from lattice generators

The Peirce blocks and graph word have distinct cosets and the proved matrix
conjugation law. The generic involutory extension constructs an injective
homomorphism on their actual octonion subgroup. Sylow conjugacy inside the
actual scalar A₅ then moves its tetrahedral centralizer to the literal `I`.

`nonempty_localEmbedding_of_generatorData` discharges these algebraic and
marking steps. Applying it to the concrete lattice construction proves
`nonempty_localEmbedding` without additional premises. The block descends
through its exact central-sign kernel, and its integral graph lift becomes an
involution in the Leech central quotient.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284, construction
of K₁ using Section 48, p.269. No natural-module classification is assumed.
-/

@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
open Matrix Atlas.SplitOctonion Atlas.Conway
open scoped MatrixGroups
open OctonionLocals PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization

/-- Extend the block map across the exact octonion graph involution, then
conjugate the scalar tetrahedral image to the literal `I`. -/
theorem nonempty_localEmbedding_of_generatorData (D : GeneratorData) :
    Nonempty LocalEmbedding := by
  let h : longLocal (F := F) →* LeechCentralQuotient :=
    InvolutoryExtension.lift blockHom D.block graph D.swap graphTwist
      graph_square D.swap_square graph_block D.swap_block block_injective graph_not_block
  have hi : Function.Injective h :=
    InvolutoryExtension.lift_injective blockHom D.block graph D.swap graphTwist
      graph_square D.swap_square graph_block D.swap_block block_injective graph_not_block
      D.block_injective D.swap_not_block
  let J := (scalarFive.comp D.marking).range
  have hm (x : longLocal (F := F)) : h x ∈ Subgroup.centralizer (J : Set _) := by
    apply InvolutoryExtension.lift_mem blockHom D.block graph D.swap graphTwist
      graph_square D.swap_square graph_block D.swap_block block_injective graph_not_block
    · intro A b hb
      obtain ⟨a, rfl⟩ := hb
      exact (D.block_commute a A).eq
    · intro b hb
      obtain ⟨a, rfl⟩ := hb
      exact (D.swap_commute a).eq
  obtain ⟨g, hg⟩ := scalar_tetrahedral_conjugate D.marking D.marking_injective
  let c := (MulAut.conj g).toMonoidHom
  refine ⟨⟨c.comp h, (MulAut.conj g).injective.comp hi, ?_⟩⟩
  intro x a ha
  have ha' : a ∈ J.map c := hg.symm ▸ ha
  obtain ⟨b, hb, rfl⟩ := ha'
  change c b * c (h x) = c (h x) * c b
  simpa only [map_mul] using congrArg c (hm x b hb)

/-- The actual octonion SL₃(4)-with-graph subgroup embeds faithfully in the
literal tetrahedral centralizer of the Leech central quotient. -/
theorem nonempty_localEmbedding : Nonempty LocalEmbedding := by
  obtain ⟨D⟩ := nonempty_generatorData
  exact nonempty_localEmbedding_of_generatorData D

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long

