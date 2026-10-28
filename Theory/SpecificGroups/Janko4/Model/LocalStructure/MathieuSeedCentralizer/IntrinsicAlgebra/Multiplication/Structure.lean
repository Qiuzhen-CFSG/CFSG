module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Checks
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The regular algebra of the ten seed operators

The kernel-checked recurrences identify 56 selected monomials; their evaluation
inverse proves independence.
The exact saved basis is a linear combination of these, and its values on the
prescribed coordinate-zero vector have an explicitly certified inverse matrix.
Hence the saved span is cyclic. Commutativity shows that any matrix commuting
with the operators is determined by its cyclic value, proving that the full
matrix commutant and the generated algebra both equal the saved span.

The coordinate source and reproduction are documented in
`IntrinsicAlgebra/source/README.md` and `Multiplication/source/README.md`.
No ambient group identification is used. The cyclic argument is the matrix
version of `CyclicCommutant.lean`.
-/

open scoped Matrix
public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open MultiplicationCertificate Module

lemma gradedBasis_eq_monomial (i : Fin 56) : gradedBasis i = operatorMonomial (basisSet i) := by
  have h : ∀ n : ℕ, ∀ hn : n < 56,
      gradedBasis ⟨n, hn⟩ = ((basisTuples.get ⟨n, hn⟩).map operator).prod := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      cases n with
      | zero =>
        change gradedBasis 0 = ((basisTuples.get 0).map operator).prod
        have hz : basisTuples.get 0 = [] := by rfl
        rw [hz, List.map_nil, List.prod_nil]
        exact gradedBasis_zero
      | succ n =>
        let j : Fin 55 := ⟨n, by omega⟩
        change gradedBasis j.succ = ((basisTuples.get j.succ).map operator).prod
        rw [gradedBasis_step, basisTuples_step, List.map_cons, List.prod_cons,
          ih (basisParents.get j).val (basisParents_lt j) (basisParents.get j).isLt]
  simpa only [operatorMonomial, basisSet_sort] using h i.val i.isLt

lemma operator_mem_generatedAlgebra (i : Fin 10) : operator i ∈ generatedAlgebra :=
  Algebra.subset_adjoin (Set.mem_range_self i)

lemma operatorMonomial_mem_generatedAlgebra (s : Finset (Fin 10)) :
    operatorMonomial s ∈ generatedAlgebra := by
  apply Subalgebra.list_prod_mem
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  exact operator_mem_generatedAlgebra i

lemma algebraBasis_mem_generatedAlgebra (i : Fin 56) : algebraBasis i ∈ generatedAlgebra := by
  rw [algebraBasis_expansion]
  apply generatedAlgebra.sum_mem
  intro j _
  apply generatedAlgebra.smul_mem
  rw [gradedBasis_eq_monomial]
  exact operatorMonomial_mem_generatedAlgebra _

lemma algebraSpan_le_generatedAlgebra : algebraSpan ≤ generatedAlgebra.toSubmodule :=
  Submodule.span_le.mpr fun _ ⟨i, hi⟩ => hi ▸ algebraBasis_mem_generatedAlgebra i

lemma generatedAlgebra_commute {a b : SmallMatrix} (ha : a ∈ generatedAlgebra)
    (hb : b ∈ generatedAlgebra) : Commute a b := by
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  apply Commute.symm
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha
  intro y hy
  obtain ⟨j, rfl⟩ := hy
  exact operator_mul_comm i j

/-- Evaluation on the prescribed cyclic column, on the full matrix space. -/
def cyclicEvaluation : SmallMatrix →ₗ[ZMod 2] SmallColumn where
  toFun A := A *ᵥ cyclicVector
  map_add' A B := Matrix.add_mulVec A B cyclicVector
  map_smul' c A := Matrix.smul_mulVec c A cyclicVector

lemma cyclicEvaluation_apply (A : SmallMatrix) (i : Fin 56) :
    cyclicEvaluation A i = A i 0 := by
  change (A *ᵥ Pi.single 0 1) i = _
  rw [Matrix.mulVec_single_one]
  rfl

lemma linearIndependent_of_evaluation_inverse (b : Fin 56 → SmallMatrix) (C D : SmallMatrix)
    (he : ∀ i j, C i j = b j i 0) (hinv : D * C = 1) : LinearIndependent (ZMod 2) b := by
  apply LinearIndependent.of_comp cyclicEvaluation
  have hinj : Function.Injective C.mulVec := by
    intro u v huv
    have h := congrArg (fun x => D *ᵥ x) huv
    simpa only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] using h
  have hc := Matrix.mulVec_injective_iff.mp hinj
  convert hc using 1
  funext i j
  exact (cyclicEvaluation_apply _ _).trans (he j i).symm

lemma algebraBasis_linearIndependent : LinearIndependent (ZMod 2) algebraBasis :=
  linearIndependent_of_evaluation_inverse _ _ _ savedEvaluation_entry savedEvaluation_inverse_mul

lemma gradedBasis_linearIndependent : LinearIndependent (ZMod 2) gradedBasis :=
  linearIndependent_of_evaluation_inverse _ _ _ gradedEvaluation_entry gradedEvaluation_inverse_mul

theorem operator_linearIndependent : LinearIndependent (ZMod 2) operator := by
  let f : Fin 10 → Fin 56 := fun i => ⟨i.val + 1, by omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Fin.val hij
    apply Fin.ext
    change i.val + 1 = j.val + 1 at hij'
    omega
  have h : ∀ i : Fin 10, basisWords.get (f i) = operatorWords.get i := by decide +kernel
  have hb : operator = gradedBasis ∘ f := by
    funext i
    exact congrArg decodeFlat (h i).symm
  rw [hb]
  exact gradedBasis_linearIndependent.comp f hf

theorem operatorSpace_finrank : Module.finrank (ZMod 2) operatorSpace = 10 := by
  let b : Basis (Fin 10) (ZMod 2) operatorSpace := Basis.span operator_linearIndependent
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b

/-- The basis is exactly the originally published family, in its saved order. -/
noncomputable def savedAlgebraBasis : Basis (Fin 56) (ZMod 2) algebraSpan :=
  Basis.span algebraBasis_linearIndependent

lemma savedAlgebraBasis_coe (i : Fin 56) : (savedAlgebraBasis i : SmallMatrix) = algebraBasis i :=
  Basis.coe_span_apply _ _

lemma algebraSpan_finrank : Module.finrank (ZMod 2) algebraSpan = 56 := by
  simpa using Module.finrank_eq_card_basis savedAlgebraBasis

lemma evaluation_sum (c : SmallColumn) :
    (∑ i : Fin 56, c i • algebraBasis i) *ᵥ cyclicVector =
      decodeFlat savedEvaluationWord *ᵥ c := by
  funext j
  rw [cyclicVector, Matrix.mulVec_single_one]
  change (∑ i : Fin 56, c i • algebraBasis i) j 0 = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    savedEvaluation_entry]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

lemma algebraSpan_cyclic (w : SmallColumn) : ∃ a ∈ algebraSpan, a *ᵥ cyclicVector = w := by
  let c := decodeFlat savedEvaluationInverseWord *ᵥ w
  refine ⟨∑ i : Fin 56, c i • algebraBasis i, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · rw [evaluation_sum]
    change decodeFlat savedEvaluationWord *ᵥ (decodeFlat savedEvaluationInverseWord *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, savedEvaluation_mul_inverse, Matrix.one_mulVec]

lemma generatedAlgebra_cyclic (w : SmallColumn) : ∃ a ∈ generatedAlgebra, a *ᵥ cyclicVector = w := by
  obtain ⟨a, ha, hw⟩ := algebraSpan_cyclic w
  exact ⟨a, algebraSpan_le_generatedAlgebra ha, hw⟩

/-- Equality of arbitrary matrices is detected on the cyclic vector once they
commute with the ten generating operators. -/
lemma matrix_eq_of_operator_commute (G H : SmallMatrix)
    (hG : ∀ i, G * operator i = operator i * G)
    (hH : ∀ i, H * operator i = operator i * H)
    (he : G *ᵥ cyclicVector = H *ᵥ cyclicVector) : G = H := by
  have hcomm (X : SmallMatrix) (hX : ∀ i, X * operator i = operator i * X)
      (a : SmallMatrix) (ha : a ∈ generatedAlgebra) : X * a = a * X :=
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha
      (fun _ ⟨i, hi⟩ => hi ▸ hX i)).eq
  have heq (w : SmallColumn) : G *ᵥ w = H *ᵥ w := by
    obtain ⟨a, ha, rfl⟩ := generatedAlgebra_cyclic w
    calc
      G *ᵥ (a *ᵥ cyclicVector) = a *ᵥ (G *ᵥ cyclicVector) := by
        simp only [Matrix.mulVec_mulVec, hcomm G hG a ha]
      _ = a *ᵥ (H *ᵥ cyclicVector) := by rw [he]
      _ = H *ᵥ (a *ᵥ cyclicVector) := by
        simp only [Matrix.mulVec_mulVec, hcomm H hH a ha]
  exact Matrix.ext_of_mulVec_single (fun i => heq (Pi.single i 1))

/-- The commutant inside the full 3136-dimensional matrix space, with no
invertibility or ambient subgroup restriction. -/
theorem commutes_operator_iff_mem_algebraSpan (G : SmallMatrix) :
    (∀ i, G * operator i = operator i * G) ↔ G ∈ algebraSpan := by
  constructor
  · intro hG
    obtain ⟨a, ha, he⟩ := algebraSpan_cyclic (G *ᵥ cyclicVector)
    have hGa : G = a := matrix_eq_of_operator_commute G a hG
      (fun i => (generatedAlgebra_commute (algebraSpan_le_generatedAlgebra ha)
        (operator_mem_generatedAlgebra i)).eq) he.symm
    exact hGa.symm ▸ ha
  · intro hG i
    exact (generatedAlgebra_commute (algebraSpan_le_generatedAlgebra hG)
      (operator_mem_generatedAlgebra i)).eq

theorem generatedAlgebra_toSubmodule_eq : generatedAlgebra.toSubmodule = algebraSpan := by
  apply le_antisymm
  · intro a ha
    exact (commutes_operator_iff_mem_algebraSpan a).mp fun i =>
      (generatedAlgebra_commute ha (operator_mem_generatedAlgebra i)).eq
  · exact algebraSpan_le_generatedAlgebra

theorem generatedAlgebra_finrank : Module.finrank (ZMod 2) generatedAlgebra = 56 := by
  change Module.finrank (ZMod 2) generatedAlgebra.toSubmodule = 56
  rw [generatedAlgebra_toSubmodule_eq, algebraSpan_finrank]

/-- Evaluation at the literal coordinate-zero column is a linear isomorphism. -/
noncomputable def algebraEvaluationEquiv : algebraSpan ≃ₗ[ZMod 2] SmallColumn :=
  LinearEquiv.ofBijective (cyclicEvaluation.comp algebraSpan.subtype) (by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact matrix_eq_of_operator_commute a b
        ((commutes_operator_iff_mem_algebraSpan a).mpr a.property)
        ((commutes_operator_iff_mem_algebraSpan b).mpr b.property) hab
    · intro w
      obtain ⟨a, ha, hw⟩ := algebraSpan_cyclic w
      exact ⟨⟨a, ha⟩, hw⟩)

set_option maxRecDepth 10000 in
theorem algebraEvaluationEquiv_apply (a : algebraSpan) :
    algebraEvaluationEquiv a = (a : SmallMatrix) *ᵥ cyclicVector := by
  rfl

set_option maxRecDepth 10000 in
lemma topOperator_eq_gradedBasis : topOperator = gradedBasis 55 := by
  have h : topOperatorWord = basisWords.get 55 := by decide +kernel
  exact congrArg decodeFlat h

theorem topOperator_ne_zero : topOperator ≠ 0 := by
  rw [topOperator_eq_gradedBasis]
  exact gradedBasis_linearIndependent.ne_zero 55

set_option maxRecDepth 10000 in
theorem topOperator_eq_product :
    topOperator = operator 0 * operator 1 * operator 2 * operator 3 := by
  rw [topOperator_eq_gradedBasis, gradedBasis_eq_monomial, operatorMonomial, basisSet_sort]
  change (operator 0 * (operator 1 * (operator 2 * (operator 3 * 1)))) = _
  simp only [mul_one, mul_assoc]

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
