module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.SplitRepresentation.Kernel.FactorAction
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.SplitNormalForm.Generation

/-!
# Faithfulness on the entire split B₂ Levi

Write an arbitrary Levi element as a positive-root word, a torus times one
of eight Weyl representatives, and another positive-root word. If its
four-space action is trivial, the explicit matrix entries force the Weyl
representative and both torus parameters to be trivial. The element therefore
belongs to the positive block. There the matrix entries recover all four root
parameters, so trivial action forces the actual group element to be one.

The normal form covers the full generated Levi, including the nonsimple
subsystem roots. No representation, kernel, or fixed-point identification is
assumed. Source: GLS3 §§2.3–2.4, for the Levi of Aschbacher–Smith F.1.12(I)(5),
printed p.263 (PDF p.274).
-/

@[expose] public noncomputable section
namespace ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
open Subgroup LocalBlockInput.PairRigidity
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.SuzukiChart
variable {m : ℕ}

/-- Trivial action forces an actual positive-block element to be the identity. -/
theorem positive_eq_one_of_fourSpace {g : SplitGroup m}
    (hg : g ∈ splitSimpleBlock m .suzuki true)
    (h : g.val.val * fourEmbedding m = fourEmbedding m) : g = 1 := by
  obtain ⟨p,rfl⟩ := splitWord_cover hg
  have he : upperMatrix p = 1 := by
    apply fourEmbedding_mul_injective
    exact (actsAs_splitWord p).symm.trans (h.trans (Matrix.mul_one _).symm)
  rw [upperMatrix_eq_one he, splitWord_zero]

/-- Faithfulness on the entire generated Levi, using its unrestricted Bruhat factors. -/
theorem splitLeviRepresentation_injective (m : ℕ) :
    Function.Injective (splitLeviRepresentation m) := by
  apply (injective_iff_map_eq_one (splitLeviRepresentation m)).mpr
  intro g hg
  have hfix := (splitLeviRepresentation_eq_one_iff g).mp hg
  change g.val.val.val * fourEmbedding m = fourEmbedding m at hfix
  obtain ⟨u,hu,n,hn,v,hv,he⟩ := SuzukiSplitNormalForm.unrestricted_factors g.property
  obtain ⟨p,rfl⟩ := splitWord_cover hu
  obtain ⟨q,rfl⟩ := splitWord_cover hv
  obtain ⟨a,b,k,rfl⟩ := SuzukiNormalizer.splitForm m n hn
  have ha := actsAs_mul (actsAs_mul (actsAs_splitWord p)
    (actsAs_mul (actsAs_torus a b) (actsAs_representative k))) (actsAs_splitWord q)
  rw [← he] at ha
  have hm : upperMatrix p * (torusMatrix a b * representativeMatrix k) * upperMatrix q = 1 := by
    apply fourEmbedding_mul_injective
    exact ha.symm.trans (hfix.trans (Matrix.mul_one _).symm)
  obtain ⟨rfl,rfl,rfl⟩ := normalizer_parameters p q a b k hm
  have hn : SuzukiNormalizer.torus (1 : (CoefficientField m)ˣ) 1 *
      SuzukiNormalizer.representative m 0 = 1 := by
    simp [SuzukiNormalizer.representative, SuzukiNormalizer.word, Parabolics.Binary.FixedGeometry.simpleWord]
  rw [hn, mul_one] at he
  apply Subtype.ext
  apply positive_eq_one_of_fourSpace _ hfix
  rw [he]
  exact mul_mem (splitWord_mem p) (splitWord_mem q)

end ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
