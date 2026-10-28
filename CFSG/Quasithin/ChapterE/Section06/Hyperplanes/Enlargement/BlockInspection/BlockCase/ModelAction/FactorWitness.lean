module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.FactorType

/-!
# The remaining factor-identification obligation in E.6.23

E.6.7 decomposes a characteristic-two intermediate group into specified
blocks. Applying its type and action clauses to the actual proper overgroup
X requires identifying X with one of those factors. This contract records
that remaining obligation, retaining the hyperplane block and corank-two
overgroup from the consumer. It is not an earlier-source theorem.

Characteristic two of the join is an explicit input here; the independent
CharacteristicTwo module proves it from E.6.21 and the genuine block
hypothesis. ModelAction retains final assembly of ProperOvergroupModels.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7,
printed p.246, and E.6.23, printed p.254 (PDF pp.257 and 265).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
open InvariantSubspaces.BlockSelection

variable {G : Type*} [Group G]

/-- Identification with an actual E.6.7 factor, still to be proved from the
permitted earlier-source inputs. This asserts neither the natural-four type
nor the Sylow-center action. -/
def ProperBlockFactors (T : Sylow 2 G) (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → (¬ L ≤ M) →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
        ∀ X : Subgroup G, L < X → CentralizerBlock A X →
          ChapterC.IsChiZeroBlock X →
            HasCharacteristicTwo (X ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G) →
              ∃ d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V A
                  (X ⊔ sylowCentralizer (T : Subgroup G) V),
                ∃ i : Fin d.count, d.block i = X

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
