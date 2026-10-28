module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Tactic.FinCases

/-!
# An elementary abelian subgroup of rank three in Ω₈⁺(2)

Three products of opposite Siegel roots give commuting elements of order three.
The roots are `e₀-f₁`, `e₀+e₁` and `e₂-f₃`, in the usual D₄ notation. Each
factor is an actual generator of the existing elementary subgroup. Their
matrices and the 27 possible products give small kernel-checked certificates
for commutation, order and independence. Squared matrices are stored separately
to keep the certificates small; the ambient group is never enumerated.

Over the binary field, a scalar squaring to one equals one. Thus the literal
projective map remains injective on the constructed subgroup. The elementary
abelian witness theorem supplies 3-rank at least three. Two opposite Siegel
roots also directly witness noncommutativity of the projective carrier.

The consumer is the Ω₈⁺(2) section in GLS3 Table 5.3l
(`refs/KGroup/GLS3/Chapter5(sec3-).tex`), used in Aschbacher–Smith A.2.15(2)
and A.2.19 (`refs/quasithin.pdf`, printed pp. 37–41). The Siegel construction
and its ATLAS attribution are retained in `SplitOdd.Elementary`.
-/

public noncomputable section
namespace ClassicalOrthogonal.BinaryEightObstruction
open Matrix

local notation "K" => ZMod 2
local notation "E" => OmegaPlus 4 (ZMod 2)
local notation "Q" => formD 4 (ZMod 2)

private def rootEF (i j : Fin 4) (h : i ≠ j) : E :=
  ⟨siegelElement Q (e i) (f j) (formD_e i)
    (by rw [polarD_f]; simp [e, Ne.symm h]), siegelElement_mem _ _ _ _ _⟩
private def rootEE (i j : Fin 4) : E :=
  ⟨siegelElement Q (e i) (e j) (formD_e i)
    (by rw [polarD_e]; simp [e]), siegelElement_mem _ _ _ _ _⟩
private def rootFF (i j : Fin 4) : E :=
  ⟨siegelElement Q (f i) (f j) (formD_f i)
    (by rw [polarD_f]; simp [f]), siegelElement_mem _ _ _ _ _⟩

private def representation : E →* Matrix (Index 4) (Index 4) K :=
  LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      ((Theory.AlgebraicGroup.quadraticIsometrySubgroup Q).subtype.comp
        (elementarySubgroup Q).subtype))

private theorem representation_injective : Function.Injective representation := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact LinearMap.toMatrixAlgEquiv'.injective h

private theorem representation_rootEF (i j : Fin 4) (h : i ≠ j) :
    representation (rootEF i j h) = 1 + Matrix.single (.inl i) (.inl j) 1 +
      Matrix.single (.inr j) (.inr i) 1 := by
  ext a b
  change Quadratic.siegel Q (e i) (f j) (Pi.single b 1) a = _
  simp only [Quadratic.siegel, polarD_f, polarD_e, formD_f, zero_mul, zero_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp [e, f, Pi.single_apply, Matrix.single, Matrix.one_apply, sub_eq_add_neg, ite_and, eq_comm]

private theorem representation_rootEE (i j : Fin 4) :
    representation (rootEE i j) = 1 + Matrix.single (.inl i) (.inr j) 1 +
      Matrix.single (.inl j) (.inr i) 1 := by
  ext a b
  change Quadratic.siegel Q (e i) (e j) (Pi.single b 1) a = _
  simp only [Quadratic.siegel, polarD_e, formD_e, zero_mul, zero_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp [e, Pi.single_apply, Matrix.single, Matrix.one_apply, sub_eq_add_neg, ite_and, eq_comm]

private theorem representation_rootFF (i j : Fin 4) :
    representation (rootFF i j) = 1 + Matrix.single (.inr i) (.inl j) 1 +
      Matrix.single (.inr j) (.inl i) 1 := by
  ext a b
  change Quadratic.siegel Q (f i) (f j) (Pi.single b 1) a = _
  simp only [Quadratic.siegel, polarD_f, formD_f, zero_mul, zero_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp [f, Pi.single_apply, Matrix.single, Matrix.one_apply, sub_eq_add_neg, ite_and, eq_comm]

private def generators : Fin 3 → E :=
  ![rootEF 0 1 (by decide) * rootEF 1 0 (by decide),
    rootEE 0 1 * rootFF 0 1,
    rootEF 2 3 (by decide) * rootEF 3 2 (by decide)]

private def generatorMatrix : Fin 3 → Matrix (Index 4) (Index 4) K :=
  ![(Matrix.fromBlocks
      !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
      !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]),
    (Matrix.fromBlocks
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]),
    (Matrix.fromBlocks
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0])]

private theorem representation_generators (i : Fin 3) :
    representation (generators i) = generatorMatrix i := by
  fin_cases i
  · change representation (rootEF 0 1 _ * rootEF 1 0 _) = _
    rw [map_mul, representation_rootEF, representation_rootEF]
    decide
  · change representation (rootEE 0 1 * rootFF 0 1) = _
    rw [map_mul, representation_rootEE, representation_rootFF]
    decide
  · change representation (rootEF 2 3 _ * rootEF 3 2 _) = _
    rw [map_mul, representation_rootEF, representation_rootEF]
    decide

private def squareMatrix : Fin 3 → Matrix (Index 4) (Index 4) K :=
  ![(Matrix.fromBlocks
      !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
      !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]),
    (Matrix.fromBlocks
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]),
    (Matrix.fromBlocks
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0]
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1])]

private theorem generatorMatrix_square : ∀ i, generatorMatrix i * generatorMatrix i = squareMatrix i := by
  decide

private theorem generatorMatrix_cube : ∀ i, squareMatrix i * generatorMatrix i = 1 := by
  decide

private theorem generators_cube (i : Fin 3) : generators i ^ 3 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, representation_generators]
  rw [pow_succ, pow_two, generatorMatrix_square, generatorMatrix_cube]

private theorem generatorMatrix_commute : ∀ i j, generatorMatrix i * generatorMatrix j =
    generatorMatrix j * generatorMatrix i := by decide

private theorem generators_commute (i j : Fin 3) : Commute (generators i) (generators j) := by
  apply representation_injective
  simpa only [map_mul, representation_generators] using generatorMatrix_commute i j

private def cycle (i : Fin 3) : Multiplicative (ZMod 3) →* E where
  toFun a := generators i ^ a.toAdd.val
  map_one' := pow_zero _
  map_mul' a b := by
    change generators i ^ (a.toAdd + b.toAdd).val = _
    rw [ZMod.val_add, ← pow_add]
    exact pow_eq_pow_of_modEq (Nat.mod_mod _ _) (generators_cube i)

private theorem cycles_commute : Pairwise (fun i j => ∀ a b,
    Commute (cycle i a) (cycle j b)) := by
  intro i j _ a b
  exact (generators_commute i j).pow_pow a.toAdd.val b.toAdd.val

/-- Three independent order-three root words in the actual elementary group. -/
def embedding : (Fin 3 → Multiplicative (ZMod 3)) →* E :=
  MonoidHom.noncommPiCoprod cycle cycles_commute

private theorem embedding_apply (a : Fin 3 → Multiplicative (ZMod 3)) :
    embedding a = generators 0 ^ (a 0).toAdd.val *
      (generators 1 ^ (a 1).toAdd.val * generators 2 ^ (a 2).toAdd.val) := by
  rw [embedding, MonoidHom.noncommPiCoprod_apply]
  have h : (Finset.univ : Finset (Fin 3)) = [0, 1, 2].toFinset := by decide
  rw [h, Finset.noncommProd_toFinset _ _ _ (by decide)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

private def powerMatrix (i : Fin 3) (a : ZMod 3) : Matrix (Index 4) (Index 4) K :=
  if a = 0 then 1 else if a = 1 then generatorMatrix i else squareMatrix i

private theorem representation_cycle (i : Fin 3) (a : Multiplicative (ZMod 3)) :
    representation (cycle i a) = powerMatrix i a.toAdd := by
  change representation (generators i ^ a.toAdd.val) = _
  rw [map_pow, representation_generators]
  generalize a.toAdd = ha
  fin_cases ha
  · exact pow_zero _
  · exact pow_one _
  · change generatorMatrix i ^ 2 = squareMatrix i
    rw [pow_two, generatorMatrix_square]

private def wordMatrix (a b c : ZMod 3) : Matrix (Index 4) (Index 4) K :=
  powerMatrix 0 a * (powerMatrix 1 b * powerMatrix 2 c)

private theorem wordMatrix_kernel : ∀ a b c, wordMatrix a b c = 1 → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide

private theorem representation_embedding (a : Fin 3 → Multiplicative (ZMod 3)) :
    representation (embedding a) = wordMatrix (a 0).toAdd (a 1).toAdd (a 2).toAdd := by
  rw [embedding_apply]
  change representation (cycle 0 (a 0) * (cycle 1 (a 1) * cycle 2 (a 2))) = _
  simp only [map_mul, representation_cycle, wordMatrix]

/-- Independence is certified in the faithful natural matrix representation. -/
theorem embedding_injective : Function.Injective embedding := by
  apply (injective_iff_map_eq_one embedding).mpr
  intro a ha
  have h := congrArg representation ha
  rw [representation_embedding, map_one] at h
  obtain ⟨h0, h1, h2⟩ := wordMatrix_kernel _ _ _ h
  funext i
  apply Multiplicative.toAdd.injective
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- In the binary field the actual scalar quotient map is injective. -/
theorem projectiveMap_injective :
    Function.Injective (projectiveElementaryMap Q) := by
  apply (injective_iff_map_eq_one (projectiveElementaryMap Q)).mpr
  intro g hg
  obtain ⟨c, hc, hscalar⟩ := (projectiveElementaryMap_eq_one_iff Q g).mp hg
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hc with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change g.val.val v = v
  rw [hscalar, hc1, one_smul]

/-- The elementary abelian subgroup followed by the literal scalar quotient. -/
def projectiveEmbedding : (Fin 3 → Multiplicative (ZMod 3)) →* POmegaPlus 4 K :=
  (projectiveElementaryMap Q).comp embedding

/-- Compatibility with the exact projective map used by `POmegaPlus`. -/
theorem projectiveEmbedding_apply (a : Fin 3 → Multiplicative (ZMod 3)) :
    projectiveEmbedding a = projectiveElementaryMap Q (embedding a) := by rfl

/-- Projectivization preserves the constructed rank-three subgroup. -/
theorem projectiveEmbedding_injective : Function.Injective projectiveEmbedding :=
  projectiveMap_injective.comp embedding_injective

/-- The embedded elementary abelian group of order 27 witnesses 3-rank at least three. -/
theorem primeRank_three_ge : 3 ≤ primeRank 3 (POmegaPlus 4 K) := by
  have hp : ∀ a : Fin 3 → (Multiplicative (ZMod 3)), a ^ 3 = 1 := by
    intro a
    funext i
    change Multiplicative.ofAdd (3 • (a i).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 3 (a i).toAdd)
  have hc : Nat.card (Fin 3 → (Multiplicative (ZMod 3))) = 3 ^ 3 := by
    simp [Nat.card_eq_fintype_card]
  exact primeRank_ge_of_elementary_embedding hp hc projectiveEmbedding
    projectiveEmbedding_injective

open scoped IsMulCommutative

/-- Opposite root transformations do not commute, even after projectivization. -/
theorem not_isMulCommutative : ¬ IsMulCommutative (POmegaPlus 4 K) := by
  intro hcomm
  let := hcomm
  have hn : representation (rootEF 0 1 (by decide) * rootEF 1 0 (by decide)) ≠
      representation (rootEF 1 0 (by decide) * rootEF 0 1 (by decide)) := by
    simp only [map_mul, representation_rootEF]
    decide
  apply hn
  apply congrArg representation
  apply projectiveMap_injective
  rw [map_mul, map_mul, mul_comm]

end ClassicalOrthogonal.BinaryEightObstruction
