module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.SplitRepresentation.Kernel.FactorMatrices
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.FixedNormalizer.Collection

/-!
# The action of the split B₂ Bruhat factors

Simple-reflection conjugation gives the two nonsimple root actions. Their
four-root product has the explicit upper unitriangular matrix. The coroot
pairings with the four half-roots give the diagonal torus matrix, and the
eight simple-reflection words give the eight Weyl permutation matrices.

All identities concern the actual ambient F₄ action at arbitrary field
parameters. They connect the proved split Bruhat factors to the matrix
separation calculation used in the faithfulness proof.
Source: GLS3 §§1.12 and 2.3–2.4, for Aschbacher–Smith F.1.12(I)(5), p.263.
-/

set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
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

private theorem actsAs_reflected (i : Fin 2) (r : F4Chevalley.Root) (t : CoefficientField m)
    (A : Matrix (Fin 4) (Fin 4) (CoefficientField m))
    (hr : ActsAs (rootGeneratorInGroup m r t) A) :
    ActsAs (rootGeneratorInGroup m
      (typeF4RootPairing.reflectionPerm
        (typeF4SimpleRootIndex (if i = 0 then 1 else 2)) r) t)
      (weylMatrix i * A * weylMatrix i) := by
  have h := actsAs_mul (actsAs_mul (actsAs_weyl i) hr) (actsAs_weyl i)
  have he := rankOneRepresentative_one_conj_root m (if i = 0 then 1 else 2) r t
  have hw : rankOneRepresentative m
      (typeF4SimpleRootIndex (if i = 0 then 1 else 2)) 1 =
      weylWord m (typeF4SimpleRootIndex (if i = 0 then 1 else 2)) 1 := by
    simp only [rankOneRepresentative, weylWord, Units.val_inv_eq_inv_val, Units.val_one]
  simp only [hw, SuzukiNormalizer.weyl_inv] at he
  exact he ▸ h

private theorem four_cases {P : Fin 4 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (j : Fin 4) : P j := by
  fin_cases j <;> assumption

private theorem actsAs_transport {g h : SplitGroup m}
    {A B : Matrix (Fin 4) (Fin 4) (CoefficientField m)}
    (hg : g = h) (hA : A = B) (ha : ActsAs g A) : ActsAs h B := by
  subst h
  subst B
  exact ha

-- Keep transport at the group and matrix interfaces during elaboration.
attribute [local irreducible] ActsAs rootGeneratorInGroup

private theorem actsAs_positive_0 (t : CoefficientField m) :
    ActsAs (X 0 t) (positiveRootMatrix 0 t) := by
  have hr : signedRoot 0 = roots 0 := by
    simp only [signedRoot, roots, Matrix.cons_val_zero]
  exact actsAs_transport (m := m)
    (congrArg (fun r => rootGeneratorInGroup m r t) hr)
    (simplePositiveMatrix_0 t) (actsAs_signedRoot 0 t)

private theorem actsAs_positive_1 (t : CoefficientField m) :
    ActsAs (X 1 t) (positiveRootMatrix 1 t) := by
  have hr : signedRoot 1 = roots 1 := by
    simp only [signedRoot, roots, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact actsAs_transport (m := m)
    (congrArg (fun r => rootGeneratorInGroup m r t) hr)
    (simplePositiveMatrix_1 t) (actsAs_signedRoot 1 t)

private theorem actsAs_positive_2 (t : CoefficientField m) :
    ActsAs (X 2 t) (positiveRootMatrix 2 t) := by
  have hs : signedRoot 1 = typeF4SimpleRootIndex 2 := by
    simp only [signedRoot, Matrix.cons_val_one, Matrix.cons_val_zero]
  have ha := actsAs_transport (m := m)
    (congrArg (fun r => rootGeneratorInGroup m r t) hs) rfl (actsAs_signedRoot 1 t)
  have h := actsAs_reflected (m := m) 0 (typeF4SimpleRootIndex 2) t
    (generatorMatrix m 1 t) ha
  have hr : typeF4RootPairing.reflectionPerm
      (typeF4SimpleRootIndex (if (0 : Fin 2) = 0 then 1 else 2))
      (typeF4SimpleRootIndex 2) = roots 2 := by
    simp only [roots, Fin.isValue, ↓reduceIte, Matrix.cons_val_two, Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons]
  exact actsAs_transport (m := m)
    (congrArg (fun r => rootGeneratorInGroup m r t) hr) (reflectedShortMatrix t) h

private theorem actsAs_positive_3 (t : CoefficientField m) :
    ActsAs (X 3 t) (positiveRootMatrix 3 t) := by
  have hs : signedRoot 0 = typeF4SimpleRootIndex 1 := by
    simp only [signedRoot, Matrix.cons_val_zero]
  have ha := actsAs_transport (m := m)
    (congrArg (fun r => rootGeneratorInGroup m r t) hs) rfl (actsAs_signedRoot 0 t)
  have h := actsAs_reflected (m := m) 1 (typeF4SimpleRootIndex 1) t
    (generatorMatrix m 0 t) ha
  have hr : typeF4RootPairing.reflectionPerm
      (typeF4SimpleRootIndex (if (1 : Fin 2) = 0 then 1 else 2))
      (typeF4SimpleRootIndex 1) = roots 3 := by
    simp only [roots, Fin.isValue, Fin.reduceEq, ↓reduceIte, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons]
  exact actsAs_transport (m := m)
    (congrArg (fun r => rootGeneratorInGroup m r t) hr) (reflectedLongMatrix t) h

theorem actsAs_positiveRoot (j : Fin 4) (t : CoefficientField m) :
    ActsAs (X j t) (positiveRootMatrix j t) :=
  four_cases (P := fun k => ActsAs (X k t) (positiveRootMatrix k t))
    (actsAs_positive_0 t) (actsAs_positive_1 t)
    (actsAs_positive_2 t) (actsAs_positive_3 t) j

theorem actsAs_splitWord (p : Fin 4 → CoefficientField m) :
    ActsAs (splitWord m p) (upperMatrix p) := by
  have h := actsAs_mul (actsAs_mul (actsAs_mul
    (actsAs_positiveRoot 0 (p 0)) (actsAs_positiveRoot 1 (p 1)))
    (actsAs_positiveRoot 2 (p 2))) (actsAs_positiveRoot 3 (p 3))
  exact actsAs_transport (splitWord_def p).symm (positiveProductMatrix p) h

private theorem scale_four (a b : (CoefficientField m)ˣ) (j : Fin 4) :
    (SuzukiNormalizer.scale a b (fourIndex j) : CoefficientField m) =
      (![b, a * b⁻¹, a⁻¹ * b, b⁻¹] : Fin 4 → CoefficientField m) j := by
  simp only [SuzukiNormalizer.scale, fourIndex, chevalleyBasisWeight]
  have h1 := four_pairing j 0
  have h2 := four_pairing j 1
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte] at h1 h2
  rw [h1, h2]
  fin_cases j <;> simp

theorem actsAs_torus (a b : (CoefficientField m)ˣ) :
    ActsAs (SuzukiNormalizer.torus a b) (torusMatrix a b) := by
  classical
  unfold ActsAs
  ext r j
  rw [mul_fourEmbedding, SuzukiNormalizer.torus_matrix, torusMatrix, Matrix.mul_diagonal]
  by_cases hr : r = fourIndex j
  · subst r
    simp [fourEmbedding, scale_four]
  · simp [Matrix.diagonal_apply, fourEmbedding, hr]

theorem actsAs_representative (k : Fin 8) :
    ActsAs (SuzukiNormalizer.representative m k) (representativeMatrix k) := by
  have h1 := actsAs_weyl (m := m) 0
  have h2 := actsAs_weyl (m := m) 1
  fin_cases k
  · simpa [SuzukiNormalizer.representative, SuzukiNormalizer.word, simpleWord,
      representativeMatrix] using (actsAs_one (m := m))
  · simpa [SuzukiNormalizer.representative, SuzukiNormalizer.word, simpleWord,
      representativeMatrix] using h1
  · simpa [SuzukiNormalizer.representative, SuzukiNormalizer.word, simpleWord,
      representativeMatrix] using h2
  · simpa [SuzukiNormalizer.representative, SuzukiNormalizer.word, simpleWord,
      representativeMatrix] using actsAs_mul h1 h2
  · simpa [SuzukiNormalizer.representative, SuzukiNormalizer.word, simpleWord,
      representativeMatrix, Matrix.cons_val_two, Matrix.cons_val_three] using actsAs_mul h2 h1
  · simpa [SuzukiNormalizer.representative, SuzukiNormalizer.word, simpleWord,
      representativeMatrix, Matrix.cons_val_two, Matrix.cons_val_three, mul_assoc] using
      actsAs_mul (actsAs_mul h1 h2) h1
  · simpa [SuzukiNormalizer.representative, SuzukiNormalizer.word, simpleWord,
      representativeMatrix, Matrix.cons_val_two, Matrix.cons_val_three, mul_assoc] using
      actsAs_mul (actsAs_mul h2 h1) h2
  · simpa [SuzukiNormalizer.representative, SuzukiNormalizer.word, simpleWord,
      representativeMatrix, Matrix.cons_val_two, Matrix.cons_val_three, mul_assoc] using
      actsAs_mul (actsAs_mul (actsAs_mul h1 h2) h1) h2


end ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
