module

public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeDerivedFromOrder
public import Stellmacher.Recognition.Parrott.NormalizerCoreDerivedOrder

/-!
# The Sylow-three fixed centralizer lies in the derived core

Let X be the ambient image of O₂(N_G(F)), and let D be its derived
subgroup in G. For every supplied Sylow three-subgroup Q of N_G(F),
the centralizer of Q in X lies in D.

The derived-core order calculation gives |D| = 64. Substituting this
into the fixed-point containment theorem discharges its remaining order
hypothesis, preserving the supplied Q and the actual subgroup maps.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.677, the deductions following N/U ≃ S₄ and the calculation of K′.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- The core centralizer of every supplied Sylow three-subgroup of the second
normalizer lies in the ambient derived core. -/
public theorem normalizer_three_centralizer_le_derived
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    X ⊓ centralizer (A : Set G) ≤ D := by
  exact d.normalizer_three_centralizer_le_derived_of_card h hN hproper Q
    (d.normalizer_core_derived_order h hN hproper)

end Stellmacher.Recognition.ParrottSecondElementaryData
