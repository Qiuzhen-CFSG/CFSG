module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Products
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Terminal
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PositiveWords

/-!
# Assembly of the squared-generator HS commutator certificate

The retained source word is (AB³AB²)⁶. Three existing common product gates
identify AB² and AB³; four new fixed products calculate its square and cube
and square that cube. The conclusion is the literal `positiveRelation` at
index six over Four, with no transposition or alternate carrier.

The kernel-checked shared, initial and terminal products discharge all seven
gates in `square_commutator_six`. No invertibility or representation hypothesis
is used. Source: HSG1-P1.M, (a,b²)⁶.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
open Certificates Commutators.SquareSix

/-- The exact numerical premises for the sixth-power commutator. -/
theorem square_commutator_six_of_products
    (hb2 : LongWords.ProductCheck 0)
    (hab2 : LongWords.ProductCheck 1)
    (hab3 : LongWords.ProductCheck 5)
    (hc : Commutators.SquareSix.ProductCheck 0)
    (hd : Commutators.SquareSix.ProductCheck 1)
    (he : Commutators.SquareSix.ProductCheck 2)
    (hi : Commutators.SquareSix.ProductCheck 3) :
    positiveRelation (Packed.eval 896 generatorRowsA)
      (Packed.eval 896 generatorRowsB) 6 = 1 := by
  let A := Packed.eval 896 generatorRowsA
  let B := Packed.eval 896 generatorRowsB
  have h₂ : B ^ 2 = Packed.eval 896 LongWords.rows02 := by
    rw [pow_two]
    exact hb2
  have h₃ : A * B ^ 2 = Packed.eval 896 LongWords.rows03 := by
    rw [h₂]
    exact hab2
  have h₇ : A * B ^ 3 = Packed.eval 896 LongWords.rows07 := by
    rw [pow_succ, ← mul_assoc, h₃]
    exact hab3
  have hC : A * B ^ 3 * A * B ^ 2 = Packed.eval 896 rowsC := by
    rw [mul_assoc (A * B ^ 3) A (B ^ 2), h₇, h₃]
    exact hc
  have hD : (Packed.eval 896 rowsC) ^ 2 = Packed.eval 896 rowsD := by
    rw [pow_two]
    exact hd
  have hE : (Packed.eval 896 rowsC) ^ 3 = Packed.eval 896 rowsE := by
    rw [pow_succ, hD]
    exact he
  change (A * B ^ 3 * A * B ^ 2) ^ 6 = 1
  rw [hC, show 6 = 3 * 2 from rfl, pow_mul, hE, pow_two]
  exact hi.trans LongWords.identityRows_eval

/-- The exact sixth power of the squared-generator commutator on the retained
degree-896 matrices, with every fixed product certified. -/
theorem square_commutator_six :
    positiveRelation (Packed.eval 896 generatorRowsA)
      (Packed.eval 896 generatorRowsB) 6 = 1 :=
  square_commutator_six_of_products
    (LongWords.shared_products 0 (by decide))
    (LongWords.shared_products 1 (by decide))
    (LongWords.shared_products 5 (by decide))
    initial_products.1 initial_products.2 terminal_products.1 terminal_products.2

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
