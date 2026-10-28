module

public import Theory.SpecificGroups.AlternatingSix.TwoPrimaryInvolutionData
public import Theory.Mathieu.M22.CentralCover.HexadPerfect
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary.Model
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic.Recognition

/-!
# Discharged source inputs for the binary and quartic M₂₂ hexad models

Perfectness of the original covering group gives perfectness of every actual
hexad preimage by odd-index transfer. The proved A₆ two-primary covering data
then supply the remaining input to both existing marked recognition theorems.
Their original quotient map, native section and natural-module marking are
unchanged. No global multiplier or construction of a quartic M₂₂ cover is used.

Source: Aschbacher–Smith I.2.2(6), printed pp.410 and 412.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
universe u
variable {K : Type u} [Group K] [Finite K] [Group.IsPerfect K]

/-- Binary recognition for the original cover and every chosen native hexad,
with the earlier local perfectness and A₆ cover inputs discharged. -/
theorem Binary.exists_hexadRecognition_of_perfect
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 2)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nonempty (Binary.HexadRecognition e hB) := by
  have hp : IsPGroup 2 (center K) := IsPGroup.of_card (n := 1) (by simpa using hZ)
  let : Group.IsPerfect (hexadPreimage e B) :=
    M22CentralCover.hexadPreimage_isPerfect e hp hB
  exact Binary.exists_hexadRecognition e hZ hB AlternatingSix.twoPrimaryInvolutionData

/-- Quartic recognition for the original cover, retaining its actual cyclic
center and every chosen native hexad. -/
theorem Quartic.exists_hexadRecognition_of_perfect [IsCyclic (center K)]
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nonempty (Quartic.HexadRecognition e hB) := by
  have hp : IsPGroup 2 (center K) := IsPGroup.of_card (n := 2) (by simpa using hZ)
  let : Group.IsPerfect (hexadPreimage e B) :=
    M22CentralCover.hexadPreimage_isPerfect e hp hB
  exact Quartic.exists_hexadRecognition e hZ hB AlternatingSix.twoPrimaryInvolutionData

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
