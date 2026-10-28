module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.Support
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint

/-!
# SL₄ multiple-support displacement

Every multiple-root highest support is adjacent or the endpoint pair. Apply
the proved initial-adjacent estimate to the original action and its diagram
reversal, which preserves faithfulness, irreducibility and the literal full
linear normalizer. The proved endpoint estimate handles the remaining pair.
Thus every nontrivial elementary cubic actor of rank at most four has common
fixed codimension strictly greater than twice its rank, including outer actors.

The source applications live separately in `FourDisplacement.Source` to avoid
a cycle with `BinaryCubicSieve`. No dimension bound, absolute irreducibility,
component cubic-ratio bound or module catalogue is assumed.

Source: Aschbacher–Smith K.3.2, printed pp.451,454–455; GM manuscript,
Propositions 4.7–4.8 and Lemma 4.5.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

open Representation
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every multiple-root highest support of a faithful irreducible binary SL₄
module satisfies the strict displacement estimate for all nontrivial elementary
cubic actors of rank at most four in its full linear normalizer. -/
theorem multiple_support_displacement
    (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ) (hi : IsIrreducible σ) :
    FourMultipleSupportDisplacement σ :=
  multiple_support_displacement_of_root_estimates σ
    (initial_adjacent_displacement σ hf hi)
    (initial_adjacent_displacement (diagramTwist σ)
      (diagramTwist_injective hf) (diagramTwist_irreducible hi))
    (endpoint_displacement σ hf hi)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
