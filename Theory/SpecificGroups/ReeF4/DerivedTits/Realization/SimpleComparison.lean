module

public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.SimpleData
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.AmbientRelations.Coordinates

/-!
# The eight signed simple-root matrices in the binary Geck representation

Every entry of the actual curves `x_{±αᵢ}(1)` agrees with the published binary
matrix. The basis has the four simple Cartan vectors first, followed by the
24 positive roots in `FixedCoordinates.RootPartition.table` order and then
their negatives. We obtain it by permuting the complete lexicographic root
enumeration of `AmbientRelations.Coordinates`.

The proof computes each root string in doubled integer Euclidean coordinates,
identifies its bottom coefficient, and evaluates the integral divided powers.
Omega conjugation reverses the root coordinates to give the negative curves.
Kernel-checked integer arithmetic compares the eight resulting matrices with
`Binary.simpleMatrix`, and scalar extension puts them over `CoefficientField 0`.
The final theorem has no matrix-comparison or recognition premise.

Source: `IntegralGeckConstruction`, GLS3, chapter 2, §§2.3–2.4, and Parrott,
*A Characterization of the Tits' Simple Group* (1972), printed p.683.
The entry argument extends the middle-node proof in
`AmbientRelations.FullMatrixComparison` to all four simple roots.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open scoped Matrix
set_option linter.unusedSimpArgs false
namespace ReeF4.DerivedTits.Realization
namespace SimpleComparison
noncomputable section
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
open ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof.AmbientComputation
abbrev node (i : Fin 4) := typeF4RootPairing_baseEquiv i
def alpha (i : Fin 4) : Fin 4 → ℤ :=
  ![![0, 2, -2, 0], ![0, 0, 2, -2], ![0, 0, 0, 2], ![1, -1, -1, -1]] i
def realVector (c : Fin 4 → ℤ) : Fin 4 → ℝ := fun k => (c k : ℝ) / 2
lemma realVector_injective : Function.Injective realVector := by
  intro c d h
  ext k
  have hk := congrFun h k
  change (c k : ℝ) / 2 = (d k : ℝ) / 2 at hk
  have hk' : (c k : ℝ) = (d k : ℝ) := by linarith
  exact_mod_cast hk'
lemma realVector_add_smul (c d : Fin 4 → ℤ) (z : ℤ) :
    realVector (c + z • d) = realVector c + z • realVector d := by
  ext k
  simp [realVector, zsmul_eq_mul, add_div, mul_div_assoc]
lemma root_node (i : Fin 4) :
    typeF4RootPairing.root (node i) = realVector (alpha i) := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [node, alpha, realVector, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three]
lemma shift_eq_iff (i : Fin 4) (r s : Fin 48) (z : ℤ) :
    typeF4RootPairing.root (enumeratedRoot s) =
      typeF4RootPairing.root (enumeratedRoot r) + z • typeF4RootPairing.root (node i) ↔
    rootCoords s = rootCoords r + z • alpha i := by
  rw [root_node]
  change realVector (rootCoords s) = realVector (rootCoords r) + z • realVector (alpha i) ↔ _
  rw [← realVector_add_smul, realVector_injective.eq_iff]
lemma shift_mem_iff (i : Fin 4) (r : Fin 48) (z : ℤ) :
    typeF4RootPairing.root (enumeratedRoot r) + z • typeF4RootPairing.root (node i) ∈
      Set.range typeF4RootPairing.root ↔
    ∃ s : Fin 48, rootCoords s = rootCoords r + z • alpha i := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨s, rfl⟩ := enumeratedRoot_bijective.surjective s
    exact ⟨s, (shift_eq_iff i r s z).mp hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨enumeratedRoot s, (shift_eq_iff i r s z).mpr hs⟩

def bot (i : Fin 4) (r : Fin 48) : ℕ :=
  if ∃ s, rootCoords s = rootCoords r + (-1 : ℤ) • alpha i then
    if ∃ s, rootCoords s = rootCoords r + (-2 : ℤ) • alpha i then 2 else 1
  else 0

lemma bot_spec : ∀ (i : Fin 4) (r : Fin 48),
    (∃ s, rootCoords s = rootCoords r + (-(bot i r : ℤ)) • alpha i) ∧
    (¬ ∃ s, rootCoords s = rootCoords r + (-((bot i r + 1 : ℕ) : ℤ)) • alpha i) := by
  decide +kernel

lemma chainBot (i : Fin 4) (r : Fin 48) :
    typeF4RootPairing.chainBotCoeff (node i) (enumeratedRoot r) = bot i r := by
  classical
  have hs := bot_spec i r
  rw [← shift_mem_iff, ← shift_mem_iff] at hs
  simp only [neg_smul, ← sub_eq_add_neg, ← Nat.cast_add, Int.cast_natCast, natCast_zsmul] at hs
  by_cases hlin : LinearIndependent ℝ
      ![typeF4RootPairing.root (node i), typeF4RootPairing.root (enumeratedRoot r)]
  · have hle := (typeF4RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin).mp hs.1
    have hlt := hs.2
    rw [typeF4RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin] at hlt
    omega
  · rw [typeF4RootPairing.chainBotCoeff_of_not_linearIndependent hlin]
    unfold bot
    split_ifs with h h2
    all_goals try rfl
    all_goals
      exfalso
      apply hlin
      apply typeF4RootPairing.linearIndependent_of_sub_mem_range_root'
      rw [← typeF4RootPairing.neg_mem_range_root_iff, neg_sub]
      have hm := (shift_mem_iff i r (-1)).mpr h
      simpa only [neg_one_smul, sub_eq_add_neg] using hm

abbrev Index := Fin 4 ⊕ Fin 48
def coord : Index ≃ F4Chevalley.BasisIndex :=
  Equiv.sumCongr typeF4RootPairing_baseEquiv rootEquiv
lemma root_eq_simple (i : Fin 4) (r : Fin 48) :
    enumeratedRoot r = (node i : F4Chevalley.Root) ↔ rootCoords r = alpha i := by
  rw [← typeF4RootPairing.root.injective.eq_iff, root_node]
  exact realVector_injective.eq_iff
lemma root_eq_neg_simple (i : Fin 4) (r : Fin 48) :
    enumeratedRoot r = -(node i : F4Chevalley.Root) ↔ rootCoords r = -alpha i := by
  rw [← typeF4RootPairing.root.injective.eq_iff]
  rw [show typeF4RootPairing.root (-(node i : F4Chevalley.Root)) =
    -typeF4RootPairing.root (node i) by
      exact (typeF4RootPairing.root_reflectionPerm _ _).trans
        (typeF4RootPairing.reflection_apply_self _)]
  change realVector (rootCoords r) = -typeF4RootPairing.root (node i) ↔ _
  rw [root_node]
  have hv : realVector (-alpha i) = -realVector (alpha i) := by
    ext k
    simp [realVector, neg_div]
  rw [← hv, realVector_injective.eq_iff]

def eLinear (i : Fin 4) : Matrix Index Index ℤ
  | .inl _, .inl _ => 0
  | .inl r, .inr c => if r = i ∧ rootCoords c = -alpha i then 1 else 0
  | .inr r, .inl c => if rootCoords r = alpha i then |typeF4CartanMatrix i c| else 0
  | .inr r, .inr c =>
      if rootCoords r = rootCoords c + alpha i then (bot i c : ℤ) + 1 else 0

def eHigher (i : Fin 4) (n : ℕ) : Matrix Index Index ℤ
  | .inr r, .inr c =>
      if rootCoords r = rootCoords c + (n : ℤ) • alpha i then ((bot i c + n).choose n : ℤ) else 0
  | _, _ => 0

lemma eLinear_entry (i : Fin 4) (r c : Index) :
    eMatrix (node i) (coord r) (coord c) = eLinear i r c := by
  classical
  cases r with
  | inl r =>
    cases c with
    | inl c => rfl
    | inr c =>
      change (if typeF4RootPairing_baseEquiv r = node i ∧
        enumeratedRoot c = -(node i : F4Chevalley.Root) then 1 else 0) = _
      simp only [root_eq_neg_simple, node, Equiv.apply_eq_iff_eq, eLinear]
  | inr r =>
    cases c with
    | inl c =>
      change (if enumeratedRoot r = (node i : F4Chevalley.Root) then
        |typeF4RootPairing_base.cartanMatrix (node i) (typeF4RootPairing_baseEquiv c)| else 0) = _
      simp only [root_eq_simple, typeF4RootPairing_base_cartan_apply, eLinear]
    | inr c =>
      simp only [eMatrix, coord, rootEquiv, Equiv.sumCongr_apply, Equiv.ofBijective_apply, Sum.map_inr,
        Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      have he := shift_eq_iff i c r 1
      simp only [one_smul] at he
      simp only [add_comm (typeF4RootPairing.root (node i)), he, chainBot, eLinear]

lemma eHigher_entry (i : Fin 4) (n : ℕ) (r c : Index) :
    eDividedPower (node i) (n + 2) (coord r) (coord c) = eHigher i (n + 2) r c := by
  classical
  cases r with
  | inl r => cases c <;> rfl
  | inr r =>
    cases c with
    | inl c => rfl
    | inr c =>
      simp only [eDividedPower, coord, rootEquiv, Equiv.sumCongr_apply,
        Equiv.ofBijective_apply, Sum.map_inr, Matrix.of_apply]
      have he := shift_eq_iff i c r ((n + 2 : ℕ) : ℤ)
      simp only [natCast_zsmul] at he
      simp only [he, chainBot, eHigher, Nat.add_assoc, natCast_zsmul]

def ePolynomial (i : Fin 4) : Matrix Index Index ℤ :=
  1 + eLinear i + eHigher i 2 + eHigher i 3

lemma ePolynomial_entry (i : Fin 4) (r c : Index) :
    eUnipotent (node i) 1 (coord r) (coord c) = ePolynomial i r c := by
  classical
  simp only [eUnipotent, one_pow, one_smul, Matrix.add_apply, eDividedPower_one,
    eLinear_entry, eHigher_entry i 0, eHigher_entry i 1, ePolynomial, Matrix.one_apply,
    Equiv.apply_eq_iff_eq]

def reverseIndex : Index → Index := Sum.map id Fin.rev

def negateIndex : F4Chevalley.BasisIndex → F4Chevalley.BasisIndex := Sum.map id Neg.neg

lemma coord_reverse (r : Index) : coord (reverseIndex r) = negateIndex (coord r) := by
  cases r with
  | inl r => rfl
  | inr r =>
    apply congrArg Sum.inr
    apply typeF4RootPairing.root.injective
    have hc : ∀ s : Fin 48, rootCoords s.rev = -rootCoords s := by decide +kernel
    change typeF4RootPairing.root (enumeratedRoot r.rev) =
      typeF4RootPairing.root (-(enumeratedRoot r))
    rw [show typeF4RootPairing.root (-(enumeratedRoot r)) =
      -typeF4RootPairing.root (enumeratedRoot r) by
        exact (typeF4RootPairing.root_reflectionPerm _ _).trans
          (typeF4RootPairing.reflection_apply_self _)]
    change realVector (rootCoords r.rev) = -realVector (rootCoords r)
    rw [hc]
    ext k
    simp [realVector, neg_div]

lemma omega_mul_entry (M : F4Chevalley.IntegralMatrix) (r c : F4Chevalley.BasisIndex) :
    (omegaMatrix (b := typeF4RootPairing_base) * M) r c = M (negateIndex r) c := by
  classical
  cases r with
  | inl r =>
    simp [Matrix.mul_apply, omegaMatrix, Fintype.sum_sum_type, Matrix.one_apply, negateIndex]
  | inr r =>
    have hneg (s : F4Chevalley.Root) :
        r = typeF4RootPairing.reflectionPerm s s ↔ s = typeF4RootPairing.reflectionPerm r r := by
      change r = -s ↔ s = -r
      constructor <;> intro h <;> simpa only [neg_neg] using (congrArg Neg.neg h).symm
    simp [Matrix.mul_apply, omegaMatrix, Fintype.sum_sum_type, Matrix.one_apply,
      negateIndex, hneg]

lemma mul_omega_entry (M : F4Chevalley.IntegralMatrix) (r c : F4Chevalley.BasisIndex) :
    (M * omegaMatrix (b := typeF4RootPairing_base)) r c = M r (negateIndex c) := by
  classical
  cases c <;>
    simp [Matrix.mul_apply, omegaMatrix, Fintype.sum_sum_type, Matrix.one_apply, negateIndex]

lemma fPolynomial_entry (i : Fin 4) (r c : Index) :
    fUnipotent (node i) 1 (coord r) (coord c) =
      ePolynomial i (reverseIndex r) (reverseIndex c) := by
  rw [fUnipotent_eq_omega, mul_omega_entry, omega_mul_entry,
    ← coord_reverse, ← coord_reverse, ePolynomial_entry]

/-- Lexicographic root positions relabelled as positive table rows, then negatives. -/
def rootPermutation : Equiv.Perm (Fin 48) where
  toFun := ![39, 47, 30, 38, 28, 43, 36, 46, 31, 29, 42, 27, 45, 41, 25, 26, 44, 37, 40, 24, 35, 34, 32, 33,
    9, 8, 10, 11, 0, 16, 13, 20, 2, 1, 17, 21, 3, 18, 5, 7, 22, 12, 19, 4, 14, 6, 23, 15]
  invFun := ![28, 33, 32, 36, 43, 38, 45, 39, 25, 24, 26, 27, 41, 30, 44, 47, 29, 34, 37, 42, 31, 35, 40, 46,
    19, 14, 15, 11, 4, 9, 2, 8, 22, 23, 21, 20, 6, 17, 3, 0, 18, 13, 10, 5, 16, 12, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def number : Index ≃ Fin 52 :=
  (Equiv.sumCongr (Equiv.refl (Fin 4)) rootPermutation).trans finSumFinEquiv

def basisNumbering : F4Chevalley.BasisIndex ≃ Fin 52 := coord.symm.trans number

lemma table_positive : ∀ (i : Fin 4) (r c : Index),
    (ePolynomial i r c : ZMod 2) =
      Binary.simpleMatrix false i (number r) (number c) := by
  decide +kernel

lemma table_negative : ∀ (i : Fin 4) (r c : Index),
    (ePolynomial i (reverseIndex r) (reverseIndex c) : ZMod 2) =
      Binary.simpleMatrix true i (number r) (number c) := by
  decide +kernel

lemma specialize_positive (i : Fin 4) :
    positiveMatrix (node i) (1 : CoefficientField 0) =
      (eUnipotent (node i) 1).map (Int.castRingHom (CoefficientField 0)) := by
  ext r c
  simp only [eUnipotent, positiveMatrix_formula, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp [Matrix.one_apply]

lemma specialize_negative (i : Fin 4) :
    negativeMatrix (node i) (1 : CoefficientField 0) =
      (fUnipotent (node i) 1).map (Int.castRingHom (CoefficientField 0)) := by
  ext r c
  simp only [fUnipotent, negativeMatrix_formula, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp [Matrix.one_apply]

lemma positive_comparison (i : Fin 4) (r c : Index) :
    positiveMatrix (node i) (1 : CoefficientField 0) (coord r) (coord c) =
      binaryScalar (Binary.simpleMatrix false i (number r) (number c)) := by
  rw [specialize_positive, Matrix.map_apply, ePolynomial_entry]
  have h := congrArg binaryScalar (table_positive i r c)
  simpa only [map_intCast, Int.coe_castRingHom] using h

lemma negative_comparison (i : Fin 4) (r c : Index) :
    negativeMatrix (node i) (1 : CoefficientField 0) (coord r) (coord c) =
      binaryScalar (Binary.simpleMatrix true i (number r) (number c)) := by
  rw [specialize_negative, Matrix.map_apply, fPolynomial_entry]
  have h := congrArg binaryScalar (table_negative i r c)
  simpa only [map_intCast, Int.coe_castRingHom] using h

lemma signed_comparison (negative : Bool) (i : Fin 4) (r c : Index) :
    (F4Chevalley.rootCurve (signedSimpleRoot negative i) (1 : CoefficientField 0)).val
      (coord r) (coord c) =
      binaryScalar (Binary.simpleMatrix negative i (number r) (number c)) := by
  cases negative
  · have h := congrArg Units.val (rootCurveUnit_simple (node i) (1 : CoefficientField 0))
    exact (congrFun (congrFun h (coord r)) (coord c)).trans (positive_comparison i r c)
  · have h := congrArg Units.val (rootCurveUnit_neg_simple (node i) (1 : CoefficientField 0))
    exact (congrFun (congrFun h (coord r)) (coord c)).trans (negative_comparison i r c)

lemma comparison : SimpleMatrixComparison basisNumbering := by
  intro negative i
  ext r c
  obtain ⟨r, rfl⟩ := number.surjective r
  obtain ⟨c, rfl⟩ := number.surjective c
  simpa only [Matrix.reindex_apply, basisNumbering, Equiv.symm_trans, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.trans_apply, Equiv.symm_apply_apply, Matrix.map_apply]
    using signed_comparison negative i r c

end
end SimpleComparison

/-- All eight actual signed simple-root curves have the published binary entries. -/
public theorem exists_simpleMatrixComparison :
    ∃ e : F4Chevalley.BasisIndex ≃ Fin 52, SimpleMatrixComparison e :=
  ⟨SimpleComparison.basisNumbering, SimpleComparison.comparison⟩

end ReeF4.DerivedTits.Realization
