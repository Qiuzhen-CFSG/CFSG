module

public import Stellmacher.Recognition.Parrott.SeedWithoutNTwo
public import Stellmacher.Recognition.Parrott.ChosenNormalizerUnrestricted

/-!
# Local inputs to Parrott's normalizer construction

The normalizer argument uses the derived-core normalizer identity and
solvability of the normalizers of the actual second elementary subgroups.
These are narrower than the ambient N₂ hypothesis. The original quasithin
Tits branch proves both from its own hypotheses.

The order-sixteen fixed-join exclusion and the order-eight center automizer
are proved without solvability in the imported extension modules. The final
second-centralizer argument remains a separate source theorem.

Source: Parrott (1972), Lemmas 2--6, printed pp.673--677.
-/

namespace Stellmacher.Recognition
open Subgroup
variable {G : Type*} [Group G] (z : G)

/-- The precise local premises used before the second-centralizer argument.
No ambient classification or recognition conclusion is included. -/
public structure ParrottLocalInputs : Prop where
  derived_normalizer :
    normalizer (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G) =
      centralizer ({z} : Set G)
  second_normalizer_solvable : ∀ d : ParrottSecondElementaryData z,
    Group.IsSolvable (normalizer (d.F : Set G))

end Stellmacher.Recognition
