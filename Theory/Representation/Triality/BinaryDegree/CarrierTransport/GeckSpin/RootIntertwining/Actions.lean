module
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.RootIntertwining.GeckColumns

/-!
# The eight signed Clifford basis calculations

For each simple vertex and each sign, evaluate conjugation on the four Cartan
images and 24 root bivectors. The sparse integral Geck columns reduce the
comparison to the isotropic Clifford relations. The checks retain every
coordinate and the full polynomial parameter, including its quadratic term.

Fixed-index commutation rules put the quadratic products in the same order;
scalar coefficient comparison then uses characteristic two. Linearity on the
coordinate basis gives the identity for every vector. No representation
faithfulness or injectivity assumption enters the proof.

The eight declarations keep each basis calculation below the default heartbeat
limit. Source: GLS3 §§1.12–1.14, especially 1.14.9(c), and §2.7.
-/

@[expose] public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace Triality.BinaryDegree.CarrierTransport.GeckSpin.RootIntertwining
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.Standard.Parabolics.RankOneMatrices
open RootPairing.SimpleGeckGroup RootPairing.IntegralGeckConstruction
open scoped Matrix
attribute [local instance] indexDecidableEq
variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

lemma intertwines_of_columns (pos : Bool) (i : Fin 4) (t : k)
    (h : ∀ j : FlatIndex,
      pointConjugation k (signedPoint k pos i t) (basisImage k (flatEquiv i j)) =
        basisImage k (flatEquiv i j) + t • linearColumn k pos i j +
          t ^ 2 • quadraticColumn k pos i j) :
    Intertwines k (signedGeck k pos i t) (signedPoint k pos i t) := by
  have he : (pointConjugation k (signedPoint k pos i t)).comp (embedding k) =
      (embedding k).comp (matrixAction k (signedGeck k pos i t)) := by
    apply (Pi.basisFun k Index).ext
    intro j
    obtain ⟨j, rfl⟩ := (flatEquiv i).surjective j
    simp only [Pi.basisFun_apply, LinearMap.comp_apply]
    change pointConjugation k (signedPoint k pos i t)
        (embedding k (Pi.single (flatEquiv i j) 1)) =
      embedding k (matrixAction k (signedGeck k pos i t) (Pi.single (flatEquiv i j) 1))
    rw [embedding_single, one_smul, geck_column]
    exact h j
  intro v
  exact LinearMap.congr_fun he v

private lemma positive_0 (t : k) (j : FlatIndex) :
    pointConjugation k (signedPoint k true 0 t) (basisImage k (flatEquiv 0 j)) =
      basisImage k (flatEquiv 0 j) + t • linearColumn k true 0 j +
        t ^ 2 • quadraticColumn k true 0 j := by
  rcases j with j | j <;> fin_cases j
  all_goals norm_num [linearColumn_inl, linearColumn_inr, quadraticColumn,
    typeDCartanMatrix, -pointConjugation_apply]
  all_goals try simp only [basisImage, Equiv.symm_apply_apply, cartan_gen, rootBivector_gen]
  all_goals norm_num [orderedRoot, rootOrder, rootOrderTable, rootEnumeration, pairEquiv, pairTable,
    signEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, -pointConjugation_apply]
  all_goals try simp only [signedPoint, Bool.false_eq_true, ↓reduceIte, positiveSimplePoint, negativeSimplePoint, map_add, conj_one,
    conj_mul, conj_gen_formula]
  all_goals norm_num [negativeRoot, negativeSimpleRoot, simpleRoot, typeDSimpleRootIndex, -pointConjugation_apply]
  all_goals try simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  all_goals try simp [pow_two, gen_sq, gen_sort, gen_opposite, add_smul, smul_add]
  all_goals try simp only [gen_sort k _ _ 1 0 (by decide), gen_sort k _ _ 2 0 (by decide),
    gen_sort k _ _ 2 1 (by decide), gen_sort k _ _ 3 0 (by decide),
    gen_sort k _ _ 3 1 (by decide), gen_sort k _ _ 3 2 (by decide), smul_smul]
  all_goals match_scalars <;> ring_nf
  all_goals try simp [CharTwo.two_eq_zero]

private lemma positive_1 (t : k) (j : FlatIndex) :
    pointConjugation k (signedPoint k true 1 t) (basisImage k (flatEquiv 1 j)) =
      basisImage k (flatEquiv 1 j) + t • linearColumn k true 1 j +
        t ^ 2 • quadraticColumn k true 1 j := by
  rcases j with j | j <;> fin_cases j
  all_goals norm_num [linearColumn_inl, linearColumn_inr, quadraticColumn,
    typeDCartanMatrix, -pointConjugation_apply]
  all_goals try simp only [basisImage, Equiv.symm_apply_apply, cartan_gen, rootBivector_gen]
  all_goals norm_num [orderedRoot, rootOrder, rootOrderTable, rootEnumeration, pairEquiv, pairTable,
    signEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, -pointConjugation_apply]
  all_goals try simp only [signedPoint, Bool.false_eq_true, ↓reduceIte, positiveSimplePoint, negativeSimplePoint, map_add, conj_one,
    conj_mul, conj_gen_formula]
  all_goals norm_num [negativeRoot, negativeSimpleRoot, simpleRoot, typeDSimpleRootIndex, -pointConjugation_apply]
  all_goals try simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  all_goals try simp [pow_two, gen_sq, gen_sort, gen_opposite, add_smul, smul_add]
  all_goals try simp only [gen_sort k _ _ 1 0 (by decide), gen_sort k _ _ 2 0 (by decide),
    gen_sort k _ _ 2 1 (by decide), gen_sort k _ _ 3 0 (by decide),
    gen_sort k _ _ 3 1 (by decide), gen_sort k _ _ 3 2 (by decide), smul_smul]
  all_goals match_scalars <;> ring_nf
  all_goals try simp [CharTwo.two_eq_zero]

private lemma positive_2 (t : k) (j : FlatIndex) :
    pointConjugation k (signedPoint k true 2 t) (basisImage k (flatEquiv 2 j)) =
      basisImage k (flatEquiv 2 j) + t • linearColumn k true 2 j +
        t ^ 2 • quadraticColumn k true 2 j := by
  rcases j with j | j <;> fin_cases j
  all_goals norm_num [linearColumn_inl, linearColumn_inr, quadraticColumn,
    typeDCartanMatrix, -pointConjugation_apply]
  all_goals try simp only [basisImage, Equiv.symm_apply_apply, cartan_gen, rootBivector_gen]
  all_goals norm_num [orderedRoot, rootOrder, rootOrderTable, rootEnumeration, pairEquiv, pairTable,
    signEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, -pointConjugation_apply]
  all_goals try simp only [signedPoint, Bool.false_eq_true, ↓reduceIte, positiveSimplePoint, negativeSimplePoint, map_add, conj_one,
    conj_mul, conj_gen_formula]
  all_goals norm_num [negativeRoot, negativeSimpleRoot, simpleRoot, typeDSimpleRootIndex, -pointConjugation_apply]
  all_goals try simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  all_goals try simp [pow_two, gen_sq, gen_sort, gen_opposite, add_smul, smul_add]
  all_goals try simp only [gen_sort k _ _ 1 0 (by decide), gen_sort k _ _ 2 0 (by decide),
    gen_sort k _ _ 2 1 (by decide), gen_sort k _ _ 3 0 (by decide),
    gen_sort k _ _ 3 1 (by decide), gen_sort k _ _ 3 2 (by decide), smul_smul]
  all_goals match_scalars <;> ring_nf
  all_goals try simp [CharTwo.two_eq_zero]

private lemma positive_3 (t : k) (j : FlatIndex) :
    pointConjugation k (signedPoint k true 3 t) (basisImage k (flatEquiv 3 j)) =
      basisImage k (flatEquiv 3 j) + t • linearColumn k true 3 j +
        t ^ 2 • quadraticColumn k true 3 j := by
  rcases j with j | j <;> fin_cases j
  all_goals norm_num [linearColumn_inl, linearColumn_inr, quadraticColumn,
    typeDCartanMatrix, -pointConjugation_apply]
  all_goals try simp only [basisImage, Equiv.symm_apply_apply, cartan_gen, rootBivector_gen]
  all_goals norm_num [orderedRoot, rootOrder, rootOrderTable, rootEnumeration, pairEquiv, pairTable,
    signEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, -pointConjugation_apply]
  all_goals try simp only [signedPoint, Bool.false_eq_true, ↓reduceIte, positiveSimplePoint, negativeSimplePoint, map_add, conj_one,
    conj_mul, conj_gen_formula]
  all_goals norm_num [negativeRoot, negativeSimpleRoot, simpleRoot, typeDSimpleRootIndex, -pointConjugation_apply]
  all_goals try simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  all_goals try simp [pow_two, gen_sq, gen_sort, gen_opposite, add_smul, smul_add]
  all_goals try simp only [gen_sort k _ _ 1 0 (by decide), gen_sort k _ _ 2 0 (by decide),
    gen_sort k _ _ 2 1 (by decide), gen_sort k _ _ 3 0 (by decide),
    gen_sort k _ _ 3 1 (by decide), gen_sort k _ _ 3 2 (by decide), smul_smul]
  all_goals match_scalars <;> ring_nf
  all_goals try simp [CharTwo.two_eq_zero]

private lemma negative_0 (t : k) (j : FlatIndex) :
    pointConjugation k (signedPoint k false 0 t) (basisImage k (flatEquiv 0 j)) =
      basisImage k (flatEquiv 0 j) + t • linearColumn k false 0 j +
        t ^ 2 • quadraticColumn k false 0 j := by
  rcases j with j | j <;> fin_cases j
  all_goals norm_num [linearColumn_inl, linearColumn_inr, quadraticColumn,
    typeDCartanMatrix, -pointConjugation_apply]
  all_goals try simp only [basisImage, Equiv.symm_apply_apply, cartan_gen, rootBivector_gen]
  all_goals norm_num [orderedRoot, rootOrder, rootOrderTable, rootEnumeration, pairEquiv, pairTable,
    signEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, -pointConjugation_apply]
  all_goals try simp only [signedPoint, Bool.false_eq_true, ↓reduceIte, positiveSimplePoint, negativeSimplePoint, map_add, conj_one,
    conj_mul, conj_gen_formula]
  all_goals norm_num [negativeRoot, negativeSimpleRoot, simpleRoot, typeDSimpleRootIndex, -pointConjugation_apply]
  all_goals try simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  all_goals try simp [pow_two, gen_sq, gen_sort, gen_opposite, add_smul, smul_add]
  all_goals try simp only [gen_sort k _ _ 1 0 (by decide), gen_sort k _ _ 2 0 (by decide),
    gen_sort k _ _ 2 1 (by decide), gen_sort k _ _ 3 0 (by decide),
    gen_sort k _ _ 3 1 (by decide), gen_sort k _ _ 3 2 (by decide), smul_smul]
  all_goals match_scalars <;> ring_nf

private lemma negative_1 (t : k) (j : FlatIndex) :
    pointConjugation k (signedPoint k false 1 t) (basisImage k (flatEquiv 1 j)) =
      basisImage k (flatEquiv 1 j) + t • linearColumn k false 1 j +
        t ^ 2 • quadraticColumn k false 1 j := by
  rcases j with j | j <;> fin_cases j
  all_goals norm_num [linearColumn_inl, linearColumn_inr, quadraticColumn,
    typeDCartanMatrix, -pointConjugation_apply]
  all_goals try simp only [basisImage, Equiv.symm_apply_apply, cartan_gen, rootBivector_gen]
  all_goals norm_num [orderedRoot, rootOrder, rootOrderTable, rootEnumeration, pairEquiv, pairTable,
    signEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, -pointConjugation_apply]
  all_goals try simp only [signedPoint, Bool.false_eq_true, ↓reduceIte, positiveSimplePoint, negativeSimplePoint, map_add, conj_one,
    conj_mul, conj_gen_formula]
  all_goals norm_num [negativeRoot, negativeSimpleRoot, simpleRoot, typeDSimpleRootIndex, -pointConjugation_apply]
  all_goals try simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  all_goals try simp [pow_two, gen_sq, gen_sort, gen_opposite, add_smul, smul_add]
  all_goals try simp only [gen_sort k _ _ 1 0 (by decide), gen_sort k _ _ 2 0 (by decide),
    gen_sort k _ _ 2 1 (by decide), gen_sort k _ _ 3 0 (by decide),
    gen_sort k _ _ 3 1 (by decide), gen_sort k _ _ 3 2 (by decide), smul_smul]
  all_goals match_scalars <;> ring_nf

private lemma negative_2 (t : k) (j : FlatIndex) :
    pointConjugation k (signedPoint k false 2 t) (basisImage k (flatEquiv 2 j)) =
      basisImage k (flatEquiv 2 j) + t • linearColumn k false 2 j +
        t ^ 2 • quadraticColumn k false 2 j := by
  rcases j with j | j <;> fin_cases j
  all_goals norm_num [linearColumn_inl, linearColumn_inr, quadraticColumn,
    typeDCartanMatrix, -pointConjugation_apply]
  all_goals try simp only [basisImage, Equiv.symm_apply_apply, cartan_gen, rootBivector_gen]
  all_goals norm_num [orderedRoot, rootOrder, rootOrderTable, rootEnumeration, pairEquiv, pairTable,
    signEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, -pointConjugation_apply]
  all_goals try simp only [signedPoint, Bool.false_eq_true, ↓reduceIte, positiveSimplePoint, negativeSimplePoint, map_add, conj_one,
    conj_mul, conj_gen_formula]
  all_goals norm_num [negativeRoot, negativeSimpleRoot, simpleRoot, typeDSimpleRootIndex, -pointConjugation_apply]
  all_goals try simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  all_goals try simp [pow_two, gen_sq, gen_sort, gen_opposite, add_smul, smul_add]
  all_goals try simp only [gen_sort k _ _ 1 0 (by decide), gen_sort k _ _ 2 0 (by decide),
    gen_sort k _ _ 2 1 (by decide), gen_sort k _ _ 3 0 (by decide),
    gen_sort k _ _ 3 1 (by decide), gen_sort k _ _ 3 2 (by decide), smul_smul]
  all_goals match_scalars <;> ring_nf
  all_goals try simp [CharTwo.two_eq_zero]

private lemma negative_3 (t : k) (j : FlatIndex) :
    pointConjugation k (signedPoint k false 3 t) (basisImage k (flatEquiv 3 j)) =
      basisImage k (flatEquiv 3 j) + t • linearColumn k false 3 j +
        t ^ 2 • quadraticColumn k false 3 j := by
  rcases j with j | j <;> fin_cases j
  all_goals norm_num [linearColumn_inl, linearColumn_inr, quadraticColumn,
    typeDCartanMatrix, -pointConjugation_apply]
  all_goals try simp only [basisImage, Equiv.symm_apply_apply, cartan_gen, rootBivector_gen]
  all_goals norm_num [orderedRoot, rootOrder, rootOrderTable, rootEnumeration, pairEquiv, pairTable,
    signEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, -pointConjugation_apply]
  all_goals try simp only [signedPoint, Bool.false_eq_true, ↓reduceIte, positiveSimplePoint, negativeSimplePoint, map_add, conj_one,
    conj_mul, conj_gen_formula]
  all_goals norm_num [negativeRoot, negativeSimpleRoot, simpleRoot, typeDSimpleRootIndex, -pointConjugation_apply]
  all_goals try simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  all_goals try simp [pow_two, gen_sq, gen_sort, gen_opposite, add_smul, smul_add]
  all_goals try simp only [gen_sort k _ _ 1 0 (by decide), gen_sort k _ _ 2 0 (by decide),
    gen_sort k _ _ 2 1 (by decide), gen_sort k _ _ 3 0 (by decide),
    gen_sort k _ _ 3 1 (by decide), gen_sort k _ _ 3 2 (by decide), smul_smul]
  all_goals match_scalars <;> ring_nf
  all_goals try simp [CharTwo.two_eq_zero]


lemma signed_columns (pos : Bool) (i : Fin 4) (t : k) (j : FlatIndex) :
    pointConjugation k (signedPoint k pos i t) (basisImage k (flatEquiv i j)) =
      basisImage k (flatEquiv i j) + t • linearColumn k pos i j +
        t ^ 2 • quadraticColumn k pos i j := by
  cases pos <;> fin_cases i
  · exact negative_0 k t j
  · exact negative_1 k t j
  · exact negative_2 k t j
  · exact negative_3 k t j
  · exact positive_0 k t j
  · exact positive_1 k t j
  · exact positive_2 k t j
  · exact positive_3 k t j

theorem signed_intertwines (pos : Bool) (i : Fin 4) (t : k) :
    Intertwines k (signedGeck k pos i t) (signedPoint k pos i t) :=
  intertwines_of_columns k pos i t (signed_columns k pos i t)

end Triality.BinaryDegree.CarrierTransport.GeckSpin.RootIntertwining
