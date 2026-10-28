module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.SplitRepresentation.Action

/-!
# Root and Weyl matrices for the four-space kernel calculation

Multiplication preserves the literal four-space intertwining equation. The
parameter-one signed simple words therefore give the two permutation matrices
of the B₂ Weyl group. The integral coroot pairings with the four half-roots
also give their exact torus weights.

These are calculations in the actual F₄ action, at arbitrary coefficient-field
parameters. Source: GLS3 §§1.12 and 2.3–2.4, for the Levi underlying
Aschbacher–Smith F.1.12(I)(5), printed p.263.
-/

@[expose] public noncomputable section
set_option linter.unusedSimpArgs false

namespace ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction
open LocalBlockInput.PairRigidity
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.SuzukiChart
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open Parabolics Binary.FixedGeometry
variable {m : ℕ}
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

def ActsAs (g : SplitGroup m) (A : Matrix (Fin 4) (Fin 4) (CoefficientField m)) : Prop :=
  g.val.val * fourEmbedding m = fourEmbedding m * A

theorem actsAs_one : ActsAs (1 : SplitGroup m) 1 := by simp [ActsAs]

theorem actsAs_mul {g h : SplitGroup m} {A B : Matrix (Fin 4) (Fin 4) (CoefficientField m)}
    (hg : ActsAs g A) (hh : ActsAs h B) : ActsAs (g * h) (A * B) := by
  change (g.val.val * h.val.val) * fourEmbedding m = _
  rw [Matrix.mul_assoc, hh, ← Matrix.mul_assoc, hg, Matrix.mul_assoc]

theorem actsAs_signedRoot (i : Fin 4) (t : CoefficientField m) :
    ActsAs (rootGeneratorInGroup m (signedRoot i) t) (generatorMatrix m i t) :=
  signedRoot_intertwines i t

def weylMatrix (i : Fin 2) : Matrix (Fin 4) (Fin 4) (CoefficientField m) :=
  if i = 0 then !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]
  else !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]

private theorem generator_weylMatrix (i : Fin 2) :
    generatorMatrix m (if i = 0 then 0 else 1) 1 *
      generatorMatrix m (if i = 0 then 2 else 3) 1 *
      generatorMatrix m (if i = 0 then 0 else 1) 1 = weylMatrix i := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [generatorMatrix, weylMatrix, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte,
      Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons,
          Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, CharTwo.add_self_eq_zero]

theorem actsAs_weyl (i : Fin 2) :
    ActsAs (weylWord m (typeF4SimpleRootIndex (if i = 0 then 1 else 2)) 1)
      (weylMatrix i) := by
  have h := actsAs_mul
    (actsAs_mul (actsAs_signedRoot (if i = 0 then 0 else 1) (1 : CoefficientField m))
      (actsAs_signedRoot (if i = 0 then 2 else 3) 1))
    (actsAs_signedRoot (if i = 0 then 0 else 1) 1)
  rw [generator_weylMatrix] at h
  fin_cases i <;>
    simpa [weylWord, signedRoot, CharTwo.neg_eq] using h

theorem four_pairing (j : Fin 4) (i : Fin 2) :
    typeF4RootPairing.pairingIn ℤ (fourRoot j)
        (typeF4SimpleRootIndex (if i = 0 then 1 else 2)) =
      (![![0,1],![1,-1],![-1,1],![0,-1]] : Fin 4 → Fin 2 → ℤ) j i := by
  apply Int.cast_injective (α := ℝ)
  change algebraMap ℤ ℝ _ = _
  rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing_pairing]
  have hs (i : Fin 2) : typeF4CorootScale
      (typeF4SimpleRootIndex (if i = 0 then 1 else 2)) =
      (if i = 0 then 1 else 2 : ℝ) := by
    fin_cases i <;> simp [typeF4CorootScale_simpleRoot]
  rw [hs]
  fin_cases i <;> fin_cases j <;>
    norm_num [fourRoot, fourSigns, halfSignVector, typeF4SimpleRoot,
      dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]


def positiveRootMatrix (j : Fin 4) (t : CoefficientField m) :
    Matrix (Fin 4) (Fin 4) (CoefficientField m) :=
  ![generatorMatrix m 0 t, generatorMatrix m 1 t,
    !![1,0,t,0; 0,1,0,t; 0,0,1,0; 0,0,0,1],
    !![1,0,0,t; 0,1,0,0; 0,0,1,0; 0,0,0,1]] j


end ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
