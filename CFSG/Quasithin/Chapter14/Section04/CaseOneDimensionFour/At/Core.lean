module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Core
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.Block

/-!
# The local closure lies in the two-core of its normalizer at the original G,T

The closure `F.U` is a 2-group by the source local setup. Since it is generated
by the conjugates of the seed under `F.H`, it is normalized by `F.H`; the
standard maximality of `O₂(F.H)` therefore gives `F.U ≤ O₂(F.H)`.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original order-32 closure is a normal 2-subgroup of its literal `H`.
This proves the forward inclusion in the source equality `U = O₂(H)`. -/
theorem source_closure_le_twoCore (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    F.U ≤ F.H.pCoreIn 2 := by
  let := setup.chosen.elementary
  have hp : IsPGroup 2 F.U :=
    (source_closure d setup structural alternatives F hne).1
  exact le_pCoreIn_of_normalizes hp F.U_le_H (le_normalizer_conjugateSpanBy V F.H)

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
