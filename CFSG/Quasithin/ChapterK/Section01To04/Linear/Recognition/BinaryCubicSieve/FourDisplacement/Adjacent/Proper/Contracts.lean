module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Branches

/-!
# Representation-theoretic inputs for proper adjacent support

The two proper adjacent weights are exchanged by the positive-root-preserving
A₃ diagram automorphism. Their separation in an irreducible module rules out
outer normalizer actors. The remaining estimate concerns literal subgroups
of SL₄(2); the normalizer reduction preserves their common fixed spaces.

These are unproved producer contracts. The assembly in `Adjacent.Proper`
retains both premises until they have been established from faithful
irreducibility. No absolute irreducibility or degree bound is assumed.

Source: Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Propositions 4.7 and 4.8(3), pp.25–28; Aschbacher–Smith K.3.2, pp.454–455.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

open Representation Representation.BinaryOffender
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The two different proper adjacent weights do not coexist in this module. -/
def ProperSupportSeparation (σ : Representation (ZMod 2) Group V) : Prop :=
  ∀ v : V, v ≠ 0 → LocalHighestVector σ {0, 1} v →
    ∀ w : V, w ≠ 0 → ¬ LocalHighestVector σ {1, 2} w

/-- The common-fixed-space estimate for the remaining literal inner actors. -/
def ProperInnerEstimate (σ : Representation (ZMod 2) Group V) : Prop :=
  ∀ v : V, v ≠ 0 → LocalHighestVector σ {0, 1} v →
    ∀ B : Subgroup Group,
    IsElementaryTwo B → IsCubic σ B → rank B ≤ 4 →
    (2 ≤ rank B ∨ ∀ c : Group, c * adjacentCentralRoot 0 1 * c⁻¹ ∉ B) →
    2 * rank B < fixedCodim σ B

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
