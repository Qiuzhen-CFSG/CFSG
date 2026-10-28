module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.SourceModel.Transport
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart.Coefficients

/-!
# The explicit short-A₂ chart in characteristic two

The faithful 52-dimensional SL3 block representation has a concrete chart on
the F4 Geck lattice. Six root coordinates are the off-diagonal matrix entries;
three symmetric blocks and their duals occupy the remaining six-root strings.
The Cartan coordinates are trace, one fixed coordinate, and two diagonal sums.
Their displayed inverse uses characteristic two; all other coordinates are
permuted. This module proves the actual linear equivalence. Its compatibility
with the signed root curves is established separately by the checked coefficient
and sparse block-action calculations.

Source: GLS3 §2.6.2, the common-lattice subsystem construction. The candidate
coordinate table was obtained from the root strings; all inverse identities
below are proved over an arbitrary field of characteristic two.
-/

open Matrix Atlas.Algebra
open TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2
open SourceBlocks
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart
noncomputable section
set_option linter.unusedSimpArgs false
variable (F : Type*) [Field F] [CharP F 2]

private def fromSix (v : Fin 6 → F) : Sym F :=
  ⟨![![v 0, v 1, v 2], ![v 1, v 3, v 4], ![v 2, v 4, v 5]], by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl⟩

@[expose] public def toCoords (v : Space F) : Index → F
  | .inl i => ![v.1 0 0 + v.1 1 1 + v.1 2 2, v.2.1 0,
      v.1 1 1 + v.1 2 2, v.1 0 0 + v.1 1 1 + v.2.1 0] i
  | .inr i => match i.val with
    | 0 => v.2.1 1
    | 1 => v.2.1 2
    | 2 => (v.2.2.2 0).val 0 0
    | 3 => (v.2.2.2 0).val 0 1
    | 4 => (v.2.2.2 0).val 1 1
    | 5 => (v.2.2.1 0).val 2 2
    | 6 => (v.2.2.1 1).val 2 2
    | 7 => (v.2.2.2 0).val 0 2
    | 8 => (v.2.2.2 0).val 1 2
    | 9 => (v.2.2.1 0).val 1 2
    | 10 => (v.2.2.1 0).val 0 2
    | 11 => (v.2.2.1 1).val 1 2
    | 12 => (v.2.2.1 1).val 0 2
    | 13 => v.1 2 0
    | 14 => v.1 2 1
    | 15 => (v.2.2.2 0).val 2 2
    | 16 => (v.2.2.1 0).val 1 1
    | 17 => (v.2.2.1 0).val 0 1
    | 18 => (v.2.2.1 0).val 0 0
    | 19 => v.2.1 3
    | 20 => (v.2.2.1 1).val 1 1
    | 21 => (v.2.2.1 1).val 0 1
    | 22 => (v.2.2.1 1).val 0 0
    | 23 => v.1 1 0
    | 24 => v.1 0 1
    | 25 => (v.2.2.2 1).val 0 0
    | 26 => (v.2.2.2 1).val 0 1
    | 27 => (v.2.2.2 1).val 1 1
    | 28 => v.2.1 4
    | 29 => (v.2.2.2 2).val 0 0
    | 30 => (v.2.2.2 2).val 0 1
    | 31 => (v.2.2.2 2).val 1 1
    | 32 => (v.2.2.1 2).val 2 2
    | 33 => v.1 1 2
    | 34 => v.1 0 2
    | 35 => (v.2.2.2 1).val 0 2
    | 36 => (v.2.2.2 1).val 1 2
    | 37 => (v.2.2.2 2).val 0 2
    | 38 => (v.2.2.2 2).val 1 2
    | 39 => (v.2.2.1 2).val 1 2
    | 40 => (v.2.2.1 2).val 0 2
    | 41 => (v.2.2.2 1).val 2 2
    | 42 => (v.2.2.2 2).val 2 2
    | 43 => (v.2.2.1 2).val 1 1
    | 44 => (v.2.2.1 2).val 0 1
    | 45 => (v.2.2.1 2).val 0 0
    | 46 => v.2.1 5
    | 47 => v.2.1 6
    | _ => 0

private def fromCoords (v : Index → F) : Space F :=
  (![![v (.inl 0) + v (.inl 2), v (.inr 24), v (.inr 34)],
     ![v (.inr 23), v (.inl 3) + v (.inl 0) + v (.inl 2) + v (.inl 1), v (.inr 33)],
     ![v (.inr 13), v (.inr 14), v (.inl 3) + v (.inl 0) + v (.inl 1)]],
   ![v (.inl 1), v (.inr 0), v (.inr 1), v (.inr 19), v (.inr 28), v (.inr 46), v (.inr 47)],
   fun i => fromSix F (![![v (.inr 18), v (.inr 17), v (.inr 10), v (.inr 16), v (.inr 9), v (.inr 5)],
       ![v (.inr 22), v (.inr 21), v (.inr 12), v (.inr 20), v (.inr 11), v (.inr 6)],
       ![v (.inr 45), v (.inr 44), v (.inr 40), v (.inr 43), v (.inr 39), v (.inr 32)]] i),
   fun i => fromSix F (![![v (.inr 2), v (.inr 3), v (.inr 7), v (.inr 4), v (.inr 8), v (.inr 15)],
       ![v (.inr 25), v (.inr 26), v (.inr 35), v (.inr 27), v (.inr 36), v (.inr 41)],
       ![v (.inr 29), v (.inr 30), v (.inr 37), v (.inr 31), v (.inr 38), v (.inr 42)]] i))

private theorem from_to (v : Space F) : fromCoords F (toCoords F v) = v := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hthree : (3 : F) = 1 := by linear_combination htwo
  apply Prod.ext
  · ext i j
    fin_cases i <;> fin_cases j
    · change (v.1 0 0 + v.1 1 1 + v.1 2 2) + (v.1 1 1 + v.1 2 2) = v.1 0 0
      ring_nf
      simp [htwo]
    · rfl
    · rfl
    · rfl
    · change ((v.1 0 0 + v.1 1 1) + v.2.1 0) +
        (v.1 0 0 + v.1 1 1 + v.1 2 2) + (v.1 1 1 + v.1 2 2) + v.2.1 0 = v.1 1 1
      ring_nf
      simp [htwo, hthree]
    · rfl
    · rfl
    · rfl
    · change ((v.1 0 0 + v.1 1 1) + v.2.1 0) +
        (v.1 0 0 + v.1 1 1 + v.1 2 2) + v.2.1 0 = v.1 2 2
      ring_nf
      simp [htwo]
  · apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · apply Prod.ext
      · funext i
        apply Subtype.ext
        ext j k
        have hs := (v.2.2.1 i).property
        fin_cases i <;> fin_cases j <;> fin_cases k <;>
          first | rfl | exact hs _ _
      · funext i
        apply Subtype.ext
        ext j k
        have hs := (v.2.2.2 i).property
        fin_cases i <;> fin_cases j <;> fin_cases k <;>
          first | rfl | exact hs _ _

private theorem to_from (v : Index → F) : toCoords F (fromCoords F v) = v := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hthree : (3 : F) = 1 := by linear_combination htwo
  funext i
  cases i with
  | inl i =>
    fin_cases i
    · change (v (.inl 0) + v (.inl 2)) +
        (v (.inl 3) + v (.inl 0) + v (.inl 2) + v (.inl 1)) +
        (v (.inl 3) + v (.inl 0) + v (.inl 1)) = v (.inl 0)
      ring_nf
      simp [htwo, hthree]
    · rfl
    · change (v (.inl 3) + v (.inl 0) + v (.inl 2) + v (.inl 1)) +
        (v (.inl 3) + v (.inl 0) + v (.inl 1)) = v (.inl 2)
      ring_nf
      simp [htwo]
    · change (v (.inl 0) + v (.inl 2)) +
        (v (.inl 3) + v (.inl 0) + v (.inl 2) + v (.inl 1)) + v (.inl 1) = v (.inl 3)
      ring_nf
      simp [htwo]
  | inr i => fin_cases i <;> rfl

private def matProjection (i j : Fin 3) : Space F →ₗ[F] F where
  toFun v := v.1 i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def fixedProjection (i : Fin 7) : Space F →ₗ[F] F where
  toFun v := v.2.1 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def symProjection (a i j : Fin 3) : Space F →ₗ[F] F where
  toFun v := (v.2.2.1 a).val i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def dualProjection (a i j : Fin 3) : Space F →ₗ[F] F where
  toFun v := (v.2.2.2 a).val i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def coordinateMap : Space F →ₗ[F] (Index → F) :=
  LinearMap.pi fun i => match i with
  | .inl i => ![matProjection F 0 0 + matProjection F 1 1 + matProjection F 2 2,
      fixedProjection F 0, matProjection F 1 1 + matProjection F 2 2,
      matProjection F 0 0 + matProjection F 1 1 + fixedProjection F 0] i
  | .inr i => match i.val with
    | 0 => fixedProjection F 1
    | 1 => fixedProjection F 2
    | 2 => dualProjection F 0 0 0
    | 3 => dualProjection F 0 0 1
    | 4 => dualProjection F 0 1 1
    | 5 => symProjection F 0 2 2
    | 6 => symProjection F 1 2 2
    | 7 => dualProjection F 0 0 2
    | 8 => dualProjection F 0 1 2
    | 9 => symProjection F 0 1 2
    | 10 => symProjection F 0 0 2
    | 11 => symProjection F 1 1 2
    | 12 => symProjection F 1 0 2
    | 13 => matProjection F 2 0
    | 14 => matProjection F 2 1
    | 15 => dualProjection F 0 2 2
    | 16 => symProjection F 0 1 1
    | 17 => symProjection F 0 0 1
    | 18 => symProjection F 0 0 0
    | 19 => fixedProjection F 3
    | 20 => symProjection F 1 1 1
    | 21 => symProjection F 1 0 1
    | 22 => symProjection F 1 0 0
    | 23 => matProjection F 1 0
    | 24 => matProjection F 0 1
    | 25 => dualProjection F 1 0 0
    | 26 => dualProjection F 1 0 1
    | 27 => dualProjection F 1 1 1
    | 28 => fixedProjection F 4
    | 29 => dualProjection F 2 0 0
    | 30 => dualProjection F 2 0 1
    | 31 => dualProjection F 2 1 1
    | 32 => symProjection F 2 2 2
    | 33 => matProjection F 1 2
    | 34 => matProjection F 0 2
    | 35 => dualProjection F 1 0 2
    | 36 => dualProjection F 1 1 2
    | 37 => dualProjection F 2 0 2
    | 38 => dualProjection F 2 1 2
    | 39 => symProjection F 2 1 2
    | 40 => symProjection F 2 0 2
    | 41 => dualProjection F 1 2 2
    | 42 => dualProjection F 2 2 2
    | 43 => symProjection F 2 1 1
    | 44 => symProjection F 2 0 1
    | 45 => symProjection F 2 0 0
    | 46 => fixedProjection F 5
    | 47 => fixedProjection F 6
    | _ => 0

omit [CharP F 2] in
private theorem coordinateMap_apply (v : Space F) : coordinateMap F v = toCoords F v := by
  funext i
  cases i with
  | inl i => fin_cases i <;> rfl
  | inr i => fin_cases i <;> rfl

/-- The explicit characteristic-two block coordinates on the full Geck lattice. -/
public def coordinateEquiv : Space F ≃ₗ[F] (Index → F) :=
  { coordinateMap F with
    invFun := fromCoords F
    left_inv := by
      intro v
      change fromCoords F (coordinateMap F v) = v
      rw [coordinateMap_apply]
      exact from_to F v
    right_inv := by
      intro v
      change coordinateMap F (fromCoords F v) = v
      rw [coordinateMap_apply]
      exact to_from F v }

open Theory.AlgebraicGroup.StandardRootSystem
open ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof.AmbientComputation

/-- The actual sparse linear chart from the faithful SL3 block action. -/
public def chart : Space F ≃ₗ[F] SourceBlocks.GeckSpace F :=
  (coordinateEquiv F).trans (LinearEquiv.funCongrLeft F F basisCoordinates.symm)

public theorem chart_apply (v : Space F) (i : Index) :
    chart F v (basisCoordinates i) = toCoords F v i := by
  change coordinateMap F v (basisCoordinates.symm (basisCoordinates i)) = _
  rw [Equiv.symm_apply_apply]
  exact congrFun (coordinateMap_apply F v) i

end
end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart
