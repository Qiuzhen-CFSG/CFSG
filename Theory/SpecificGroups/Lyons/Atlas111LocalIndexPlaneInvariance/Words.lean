module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlane
/-!
# Transport reductions for the literal Lyons local words

The expanded ATLAS program expresses both local generators as conjugates.
Transporting a seven-column matrix through the conjugating word reduces
invariance to the middle word. Cancellation takes place in the actual group,
so no numerical inverse certificate is required.

Source: `Atlas111OrderSource/LyG1-max1W1`, expanded in `Atlas111OrderSetup`.
-/

namespace Lyons.OrderCertificate.PlaneTransport
public abbrev Columns := Matrix (Fin 111) (Fin 7) (ZMod 5)
@[expose] public def wordA : LyonsGroup := generatorA * generatorB * generatorA * generatorB ^ 3
@[expose] public def wordB : LyonsGroup := generatorA * generatorB * generatorA * generatorB * generatorA * generatorB ^ 2
@[expose] public def wordC : LyonsGroup := wordB * generatorA * generatorB

public theorem power_step (g : LyonsGroup) (n : ℕ) (u v w : Columns)
    (h : matrixRepresentation (g ^ n) * u = v)
    (hstep : matrixRepresentation g * v = w) :
    matrixRepresentation (g ^ (n + 1)) * u = w := by
  rw [pow_succ', map_mul, Matrix.mul_assoc, h, hstep]

public theorem localA_of_transport (v : Columns)
    (h : matrixRepresentation (wordA ^ 7) * v = separationPlaneColumns)
    (ha : matrixRepresentation generatorA * v = v * separationPlaneActionA) :
    matrixRepresentation localA * separationPlaneColumns =
      separationPlaneColumns * separationPlaneActionA := by
  have hi : matrixRepresentation ((wordA ^ 7)⁻¹) * separationPlaneColumns = v := by
    rw [← h, ← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
  rw [localA, max1Program_fst]
  change matrixRepresentation (wordA ^ 7 * generatorA * (wordA ^ 7)⁻¹) *
    separationPlaneColumns = separationPlaneColumns * separationPlaneActionA
  rw [map_mul, map_mul, Matrix.mul_assoc, hi, Matrix.mul_assoc, ha,
    ← Matrix.mul_assoc, h]

public theorem localB_of_transport (v : Columns)
    (h : matrixRepresentation (wordB ^ 25) * separationPlaneColumns = v)
    (hc : matrixRepresentation (wordC ^ 3) * v = v * separationPlaneActionB) :
    matrixRepresentation localB * separationPlaneColumns =
      separationPlaneColumns * separationPlaneActionB := by
  have hi : matrixRepresentation ((wordB ^ 25)⁻¹) * v = separationPlaneColumns := by
    rw [← h, ← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
  rw [localB, max1Program_snd]
  change matrixRepresentation ((wordB ^ 25)⁻¹ * wordC ^ 3 * wordB ^ 25) *
    separationPlaneColumns = separationPlaneColumns * separationPlaneActionB
  rw [map_mul, map_mul, Matrix.mul_assoc, h, Matrix.mul_assoc, hc,
    ← Matrix.mul_assoc, hi]
end Lyons.OrderCertificate.PlaneTransport
