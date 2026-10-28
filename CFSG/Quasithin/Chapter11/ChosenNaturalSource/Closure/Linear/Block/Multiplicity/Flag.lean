module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity.Fixed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Cardinalities

/-!
# The SL₃ seed and the original point order

The third space of the actual field flag has the full dimension three,
so its preimage is V. The point has order q because the fixed part of
the original chosen natural module vanishes. These identifications
connect the V₃-closure of 11.5.5 to the V-closure of the SL₃ branch.
Source: Aschbacher--Smith, 11.5.7, printed pp.781--782.
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)
  (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
  (f : InvariantFlag (.sl3 m))

theorem seed_eq (hthree : E.threeSpace = (Coordinates.sl3 m).binarySubspace (f.space 2)) :
    E.V₃ = V := by
  change D.centralQuotientPreimage E.threeSpace = V
  rw [hthree]
  exact InvariantFlag.sl3_top m f

theorem localClosure_eq (hthree : E.threeSpace = (Coordinates.sl3 m).binarySubspace (f.space 2)) :
    E.localClosure E.G₁ = E.W := by
  change conjugateSpanBy E.V₃ E.G₁ = conjugateSpanBy V E.G₁
  rw [seed_eq E m f hthree]

theorem point_card {x y : G}
    (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace (f.space 0)) :
    Nat.card E.V₁ = 2 ^ E.input.field.degree := by
  change Nat.card (D.centralQuotientPreimage E.point) = _
  rw [hpoint]
  change Nat.card ((Coordinates.sl3 m).preimage (f.space 0)) = _
  rw [Nonabelian.card_preimage _ (chosen_fixed_eq_bot E d), f.dimension]
  simp

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity
