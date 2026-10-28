module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.Actors
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.LocalData
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.LocalData

/-!
# The remaining binary multiple-support displacement estimates

The local highest-vector support is determined by explicit root operators.
For support of size at least two, the needed estimate says that every
nontrivial cubic elementary actor moves more than twice its rank. The actor
belongs to the full linear normalizer, so the estimate includes graph actors.
Its rank is bounded by the proved source-actor reduction.

These definitions specify independent proof obligations, not established
classifications. `BinaryCubicSieve` proves their conditional applications to
the original Chapter K hypotheses and the existing small-module consumers.
Source: Aschbacher–Smith, K.3.2; GM04 Table 7. The available GM author manuscript
separates the inner and outer arguments as Propositions 4.7 and 4.8.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve

open Representation Representation.BinaryOffender

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The precise displacement estimate needed on multiple-root SL₄ supports.
This is a contract to be proved, with neither a degree bound nor a module list
as an input. -/
def FourMultipleSupportDisplacement
    (σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) V) : Prop :=
  ∀ (J : Finset (Fin 3)) (v : V), v ≠ 0 →
    ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.LocalHighestVector
      σ J v →
    2 ≤ J.card → ∀ A : Subgroup (linearNormalizer σ),
    IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A → rank A ≤ 4 →
    2 * rank A < fixedCodim (normalizerRepresentation σ) A

/-- The independent displacement estimate for multiple-root SL₅ supports.
Irreducibility and faithfulness will be hypotheses of its producer. -/
def FiveMultipleSupportDisplacement
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) : Prop :=
  ∀ (J : Finset (Fin 4)) (v : V), v ≠ 0 →
    SL5TenDimensional.Classification.LocalHighestVector σ J v →
    2 ≤ J.card → ∀ A : Subgroup (linearNormalizer σ),
    IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A → rank A ≤ 6 →
    2 * rank A < fixedCodim (normalizerRepresentation σ) A

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve
