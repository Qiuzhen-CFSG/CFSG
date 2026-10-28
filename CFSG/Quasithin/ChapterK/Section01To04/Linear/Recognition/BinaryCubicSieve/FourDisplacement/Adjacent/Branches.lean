module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.RootNorm


/-!
# The two remaining initial-adjacent support estimates

A support containing 0 and 1 is either {0,1} or all three simple roots.
These independent contracts retain the entire linear normalizer. The
central-root rank-one case has already been removed. In full support,
`RootNorm` additionally excludes actors containing either conjugate
end-node radical. The assembly supplies this avoidance from cubicity.

These definitions are remaining proof obligations, not module
classification theorems. Faithfulness and irreducibility are to be used
by their producers; no degree or module-list premise is introduced.

Source: Aschbacher–Smith K.3.2, printed pp.454–455; GM author manuscript
Propositions 4.7 and 4.8(3B).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

open Representation Representation.BinaryOffender
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The actor configurations not settled by the existing central-root rank-one bound. -/
def RemainingAdjacentActor (σ : Representation (ZMod 2) Group V)
    (A : Subgroup (linearNormalizer σ)) : Prop :=
  2 ≤ rank A ∨ ∀ c : Group,
    componentEmbedding σ (c * adjacentCentralRoot 0 1 * c⁻¹) ∉ A

/-- The proper initial adjacent support, with all normalizer actors retained. -/
def ProperAdjacentRemainingActors (σ : Representation (ZMod 2) Group V) : Prop :=
  ∀ (v : V), v ≠ 0 → LocalHighestVector σ {0, 1} v →
    ∀ A : Subgroup (linearNormalizer σ),
    IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A → rank A ≤ 4 →
    RemainingAdjacentActor σ A →
    2 * rank A < fixedCodim (normalizerRepresentation σ) A

/-- Full support after removing the rank-one central-root case and the
two conjugate radical configurations excluded by cubicity in `RootNorm`. -/
def FullSupportRemainingActors (σ : Representation (ZMod 2) Group V) : Prop :=
  ∀ (v : V), v ≠ 0 → LocalHighestVector σ Finset.univ v →
    ∀ A : Subgroup (linearNormalizer σ),
    IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A → rank A ≤ 4 →
    RemainingAdjacentActor σ A →
    (∀ (dual : Bool) (c : Group), ¬ ∀ k : Fin 3,
      componentEmbedding σ (c * fullSupportRadicalRoot dual k * c⁻¹) ∈ A) →
    2 * rank A < fixedCodim (normalizerRepresentation σ) A


end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
