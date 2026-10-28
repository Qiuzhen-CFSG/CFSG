module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.CubicInvariant.E7Block.Operators
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.AdjointBlocks.DividedPowers
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.CubicInvariant.Transport

/-!
# Signed simple curves and words on the concrete E7 block

The integral simple operators square to zero on this block. Factorial
cancellation is performed over ℤ, so higher divided powers vanish after every
specialization, including characteristic three. The resulting literal generator
identities extend to the actual six-node word evaluation.
Source: GLS3 §2.6.2, supporting the cubic central-character calculation in
§§1.12.5–6 and Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup Matrix
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.E7Block
attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _

private theorem operatorMatrix_pow_zero (s : Bool) (i : Fin 6) (n : ℕ) (hn : 2 ≤ n) :
    operatorMatrix s i ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, operatorMatrix_square, zero_mul]

/-- Integral factorial cancellation removes every divided power of degree at least two. -/
theorem dividedPower_higher (s : Bool) (i : Fin 6) (n : ℕ) (hn : 2 ≤ n) :
    (simpleFamily (b := typeE7RootPairing_base)).dividedPower (s, e7Node i) n * AdjointBlocks.inclusion index = 0 := by
  have ha : operatorMatrix s i ^ n = n.factorial • (0 : Matrix (Fin 27) (Fin 27) ℤ) := by
    rw [operatorMatrix_pow_zero s i n hn, smul_zero]
  have hb : (if s then eMatrix (e7Node i) else fMatrix (e7Node i)) ^ n =
      n.factorial • (simpleFamily (b := typeE7RootPairing_base)).dividedPower (s, e7Node i) n := by
    cases s
    · exact fMatrix_pow_eq_factorial_smul _ _
    · exact eMatrix_pow_eq_factorial_smul _ _
  have h := AdjointBlocks.dividedPower_intertwines _ _ _
    (operator_intertwines s i) n _ _ ha hb
  simpa using h

private theorem coefficient_one (R : Type*) [CommRing R] (s : Bool) (i : Fin 6) :
    (simpleFamily (b := typeE7RootPairing_base)).coefficient (S := R) (s, e7Node i) 1 * AdjointBlocks.inclusionOver index R =
      AdjointBlocks.inclusionOver index R * (operatorMatrix s i).map (Int.castRingHom R) := by
  have h := congrArg (fun A => A.map (Int.castRingHom R)) (operator_intertwines s i)
  cases s <;>
    simpa only [Matrix.map_mul, AdjointBlocks.inclusionOver,
      IntegralCubicFamily.coefficient, simpleFamily, eDividedPower_one, fDividedPower_one,
      Bool.false_eq_true, Bool.true_eq, ↓reduceIte] using h

private theorem coefficient_higher (R : Type*) [CommRing R] (s : Bool) (i : Fin 6)
    (n : ℕ) (hn : 2 ≤ n) :
    (simpleFamily (b := typeE7RootPairing_base)).coefficient (S := R) (s, e7Node i) n * AdjointBlocks.inclusionOver index R = 0 := by
  have h := congrArg (fun A => A.map (Int.castRingHom R)) (dividedPower_higher s i n hn)
  simpa only [Matrix.map_mul, AdjointBlocks.inclusionOver,
    IntegralCubicFamily.coefficient,
    Matrix.map_zero _ (map_zero (Int.castRingHom R))] using h

/-- The literal signed E7 simple curves preserve and act correctly on the constructed block. -/
theorem simple_J (F : Type*) [Field F] (s : Bool) (i : Fin 6) (t : F) (x : Fin 27 → F) :
    (e7Simple F s (i.castLE (by decide)) t).val.val *ᵥ J F x =
      J F (CubicModel.curve s i t x) := by
  have hc : (simpleFamily (b := typeE7RootPairing_base)).curve (s, e7Node i) t * AdjointBlocks.inclusionOver index F =
      AdjointBlocks.inclusionOver index F +
        t • (AdjointBlocks.inclusionOver index F *
          (operatorMatrix s i).map (Int.castRingHom F)) := by
    simp only [IntegralCubicFamily.curve, Matrix.add_mul, Matrix.one_mul,
      Matrix.smul_mul, coefficient_one, coefficient_higher F s i 2 (by decide),
      coefficient_higher F s i 3 (by decide), smul_zero, add_zero]
  change (signedSimple F s (e7Node i) t).val.val *ᵥ J F x = _
  rw [signedSimple_val]
  change (simpleFamily (b := typeE7RootPairing_base)).curve (s, e7Node i) t *ᵥ
    (AdjointBlocks.inclusionOver index F *ᵥ x) = J F (CubicModel.curve s i t x)
  rw [Matrix.mulVec_mulVec, hc]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    operatorMatrix_mulVec, CubicModel.curve, map_add, map_smul]
  rfl

/-- Actual word intertwining, including inverse letters, with no block hypothesis. -/
theorem word_J (F : Type*) [Field F] (w : SixNodeWord F) (x : Fin 27 → F) :
    (e7Six F w).val.val *ᵥ J F x = J F (CubicModel.evaluation w x) := by
  apply CubicModel.evaluation_intertwines (J F)
    ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e7Six F))
  intro s i t y
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, e7Six_of] using simple_J F s i t y

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.E7Block
