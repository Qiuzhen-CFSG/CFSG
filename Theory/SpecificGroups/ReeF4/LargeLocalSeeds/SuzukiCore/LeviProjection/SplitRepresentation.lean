module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.FixedDescent
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.SplitRepresentation.Kernel

/-!
# A faithful general-field representation of the split B₂ Levi

The actual action on four half-root lines sends the signed simple roots at
nodes 1, 2, −1, −2 to the specified matrices, at every field parameter.
Simple-reflection conjugation supplies both nonsimple roots and their negatives,
so the paired range calculation covers the full root-defined split Levi.

Faithfulness follows from its unrestricted Bruhat factors. Matrix entries
exclude every nonidentity Weyl representative and recover both torus
parameters. The remaining kernel element lies in the positive four-root block,
where four entries recover all four root parameters. This proves injectivity
on the whole Levi, without an assumed representation or kernel property.

The construction works for every `m`; in particular it supplies the faithful
split comparison required for the large Ree groups with `m ≥ 1`. The separate
matrix-diagonal identification remains with the Suzuki projection assembly.
Source: the B₂ Levi in Aschbacher–Smith F.1.12(I)(5), printed p.263 (PDF p.274),
and the Bruhat and Chevalley relations of GLS3 §§2.3–2.4.
-/

public section
namespace ReeF4.LargeLocalSeeds.SuzukiLeviProjection
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration

/-- The actual faithful split representation, its paired range, and its literal
signed simple-root images, with no extra comparison assumptions. -/
theorem exists_faithful_splitRepresentation {m : ℕ} (d : LocalBlockInput m) :
    ∃ f : splitLevi m .suzuki →* MatrixGroup m,
      Function.Injective f ∧ (pairedMap d f).range = pairedSubgroup m ∧
      ∀ (i : Fin 4) (t : CoefficientField m),
        f (SplitRepresentation.splitGenerator m (i, t)) = matrixGenerator m i t := by
  refine ⟨SplitRepresentation.splitLeviRepresentation m,
    SplitRepresentation.splitLeviRepresentation_injective m,
    SplitRepresentation.pairedMap_range d, ?_⟩
  intro i t
  exact SplitRepresentation.splitLeviRepresentation_generator (i, t)

end ReeF4.LargeLocalSeeds.SuzukiLeviProjection
