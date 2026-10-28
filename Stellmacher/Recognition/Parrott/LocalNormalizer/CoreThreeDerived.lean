module

public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeDerived
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.NormalizerCoreSolvable
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreDerivedOrder
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreThreeDerivedFromOrder

/-!
# The actual second normalizer from local inputs

These calculations retain the supplied second elementary subgroup and Sylow.
The original derived-core normalizer identity and solvability of the actual
second normalizer replace the ambient N₂ assumption. All subgroup images,
centers, omega subgroups and conjugators are the original literal ones.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678. This is the local-input extension of `NormalizerCoreThreeDerived`.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- The core centralizer of every supplied Sylow three-subgroup of the second
normalizer lies in the ambient derived core. -/
public theorem normalizer_three_centralizer_le_derived_of_local_inputs
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    X ⊓ centralizer (A : Set G) ≤ D := by
  exact d.normalizer_three_centralizer_le_derived_of_card_of_local_inputs h hlocal hproper Q
    (d.normalizer_core_derived_order_of_local_inputs h hlocal hproper)

end Stellmacher.Recognition.ParrottSecondElementaryData
