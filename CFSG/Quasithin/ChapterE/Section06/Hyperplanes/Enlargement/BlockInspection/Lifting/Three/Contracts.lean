module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.LocalFacts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Obligations
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.LayerKernel

/-!
# The two remaining solvable lifting obligations

These are new mathematical obligations, not earlier-source inputs. First,
the A₃ block must either lie in an ordinary component of H₀ = C_G(A), or
centralize E(H₀). In the latter case the second obligation constructs a
genuine chi-zero block inside R = C_H₀(E(H₀))Q. The proved layer-kernel
argument supplies F*(R) = O₂(R) and transfers the constructed block to H₀.

The obligations can be investigated independently: the second takes the
layer-centralizing placement as its explicit local hypothesis. Their parent
retains the task of proving ThreeBlockLifting from the permitted earlier
source results. Neither the A₄ isomorphism nor membership in the perfect
C-component family is assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265); Definition 1.2.3 and Lemma 1.2.4, p.505.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three
open ComponentBalance

variable {G : Type*} [Group G]

/-- The mixed-component localization still needed for the A₃ repair. -/
def LayerPlacement (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → ChapterC.IsAlternatingBlock L 3 → (¬ L ≤ M) →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
        L ≤ layerKernel (centralizer (A : Set G)) ∨
          ∃ X : Subgroup G, L ≤ X ∧ CentralizerComponent A X

/-- Construction of an actual block in the characteristic-two envelope.
Its relative subnormality and its literal chi-zero module are both required. -/
def EnvelopeBlockDetection (Q M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → ChapterC.IsAlternatingBlock L 3 → (¬ L ≤ M) →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
        L ≤ layerKernel (centralizer (A : Set G)) →
          ∃ X : Subgroup G, L ≤ X ∧
            X ≤ layerEnvelope (centralizer (A : Set G)) Q ∧
            ChapterC.IsBlock
              (X.subgroupOf (layerEnvelope (centralizer (A : Set G)) Q)) ∧
            ChapterC.IsChiZeroBlock X

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three
