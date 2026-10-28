module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.Words
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.AmbientRelations.Coordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.AmbientRelations.ComparisonMap

/-!
# Full binary matrices of the four middle-node Geck generators

The actual integral Geck matrices at nodes 1+, 2+, 1− and 2− reduce to the
52-dimensional binary tables under the complete Cartan-plus-root coordinate
bijection. The root enumeration certifies every root-string coefficient;
kernel-checked integer arithmetic then checks all entries, including the
second and third divided powers. Geck's omega conjugation supplies the
negative generators by reversing the root coordinates and fixing the Cartan
coordinates. Finally, scalar extension identifies these matrices with the
actual ambient Levi generators over `CoefficientField 0`.

Source: the integral simple-root formulas in `IntegralGeckConstruction` and
`SimpleGeckGroup`, in the middle Levi used in Aschbacher–Smith F.1.12(I)(5),
printed pp.263–264 (PDF pp.274–275) of `refs/quasithin.pdf`.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open scoped Matrix
set_option linter.unusedSimpArgs false
namespace ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof
namespace FullComparison
noncomputable section
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
open AmbientComputation
abbrev nodeIndex (i : Fin 2) : Fin 4 := ![1, 2] i
abbrev node (i : Fin 2) := typeF4RootPairing_baseEquiv (nodeIndex i)
def alpha (i : Fin 2) : Fin 4 → ℤ := ![![0, 0, 2, -2], ![0, 0, 0, 2]] i
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
lemma root_node (i : Fin 2) :
    typeF4RootPairing.root (node i) = realVector (alpha i) := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [node, nodeIndex, alpha, realVector, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three]
lemma shift_eq_iff (i : Fin 2) (r s : Fin 48) (z : ℤ) :
    typeF4RootPairing.root (enumeratedRoot s) =
      typeF4RootPairing.root (enumeratedRoot r) + z • typeF4RootPairing.root (node i) ↔
    rootCoords s = rootCoords r + z • alpha i := by
  rw [root_node]
  change realVector (rootCoords s) = realVector (rootCoords r) + z • realVector (alpha i) ↔ _
  rw [← realVector_add_smul, realVector_injective.eq_iff]
lemma shift_mem_iff (i : Fin 2) (r : Fin 48) (z : ℤ) :
    typeF4RootPairing.root (enumeratedRoot r) + z • typeF4RootPairing.root (node i) ∈
      Set.range typeF4RootPairing.root ↔
    ∃ s : Fin 48, rootCoords s = rootCoords r + z • alpha i := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨s, rfl⟩ := enumeratedRoot_bijective.surjective s
    exact ⟨s, (shift_eq_iff i r s z).mp hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨enumeratedRoot s, (shift_eq_iff i r s z).mpr hs⟩

def bot (i : Fin 2) (r : Fin 48) : ℕ :=
  if ∃ s, rootCoords s = rootCoords r + (-1 : ℤ) • alpha i then
    if ∃ s, rootCoords s = rootCoords r + (-2 : ℤ) • alpha i then 2 else 1
  else 0

lemma bot_spec : ∀ (i : Fin 2) (r : Fin 48),
    (∃ s, rootCoords s = rootCoords r + (-(bot i r : ℤ)) • alpha i) ∧
    (¬ ∃ s, rootCoords s = rootCoords r + (-((bot i r + 1 : ℕ) : ℤ)) • alpha i) := by
  decide +kernel

lemma chainBot (i : Fin 2) (r : Fin 48) :
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
lemma coord_fin (r : Index) : basisEquiv (finSumFinEquiv r) = coord r := by
  cases r with
  | inl r => exact basisEquiv_cartan r
  | inr r => exact basisEquiv_root r

lemma root_eq_simple (i : Fin 2) (r : Fin 48) :
    enumeratedRoot r = (node i : F4Chevalley.Root) ↔ rootCoords r = alpha i := by
  rw [← typeF4RootPairing.root.injective.eq_iff, root_node]
  exact realVector_injective.eq_iff
lemma root_eq_neg_simple (i : Fin 2) (r : Fin 48) :
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

def eLinear (i : Fin 2) : Matrix Index Index ℤ
  | .inl _, .inl _ => 0
  | .inl r, .inr c => if r = nodeIndex i ∧ rootCoords c = -alpha i then 1 else 0
  | .inr r, .inl c => if rootCoords r = alpha i then |typeF4CartanMatrix (nodeIndex i) c| else 0
  | .inr r, .inr c =>
      if rootCoords r = rootCoords c + alpha i then (bot i c : ℤ) + 1 else 0

def eHigher (i : Fin 2) (n : ℕ) : Matrix Index Index ℤ
  | .inr r, .inr c =>
      if rootCoords r = rootCoords c + (n : ℤ) • alpha i then ((bot i c + n).choose n : ℤ) else 0
  | _, _ => 0

lemma eLinear_entry (i : Fin 2) (r c : Index) :
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

lemma eHigher_entry (i : Fin 2) (n : ℕ) (r c : Index) :
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

def ePolynomial (i : Fin 2) : Matrix Index Index ℤ :=
  1 + eLinear i + eHigher i 2 + eHigher i 3

lemma ePolynomial_entry (i : Fin 2) (r c : Index) :
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

lemma fPolynomial_entry (i : Fin 2) (r c : Index) :
    fUnipotent (node i) 1 (coord r) (coord c) =
      ePolynomial i (reverseIndex r) (reverseIndex c) := by
  rw [fUnipotent_eq_omega, mul_omega_entry, omega_mul_entry,
    ← coord_reverse, ← coord_reverse, ePolynomial_entry]

lemma table_positive : ∀ (i : Fin 2) (r c : Index),
    (ePolynomial i r c : ZMod 2) =
      generator (Fin.castAdd 2 i) (finSumFinEquiv r) (finSumFinEquiv c) := by
  decide +kernel

lemma table_negative : ∀ (i : Fin 2) (r c : Index),
    (ePolynomial i (reverseIndex r) (reverseIndex c) : ZMod 2) =
      generator (Fin.natAdd 2 i) (finSumFinEquiv r) (finSumFinEquiv c) := by
  decide +kernel

lemma specialize_positive (i : Fin 2) :
    positiveMatrix (node i) (1 : CoefficientField 0) =
      (eUnipotent (node i) 1).map (Int.castRingHom (CoefficientField 0)) := by
  ext r c
  simp only [eUnipotent, positiveMatrix_formula, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp [Matrix.one_apply]

lemma specialize_negative (i : Fin 2) :
    negativeMatrix (node i) (1 : CoefficientField 0) =
      (fUnipotent (node i) 1).map (Int.castRingHom (CoefficientField 0)) := by
  ext r c
  simp only [fUnipotent, negativeMatrix_formula, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp [Matrix.one_apply]

lemma positive_comparison (i : Fin 2) :
    positiveMatrix (node i) (1 : CoefficientField 0) =
      fullMatrixMap basisEquiv (generator (Fin.castAdd 2 i)) := by
  ext r c
  obtain ⟨r, rfl⟩ := coord.surjective r
  obtain ⟨c, rfl⟩ := coord.surjective c
  rw [specialize_positive, Matrix.map_apply, ePolynomial_entry]
  rw [← coord_fin r, ← coord_fin c, fullMatrixMap_apply]
  have h := congrArg (ZMod.castHom (dvd_refl 2) (CoefficientField 0)) (table_positive i r c)
  simpa only [map_intCast, Int.coe_castRingHom] using h

lemma negative_comparison (i : Fin 2) :
    negativeMatrix (node i) (1 : CoefficientField 0) =
      fullMatrixMap basisEquiv (generator (Fin.natAdd 2 i)) := by
  ext r c
  obtain ⟨r, rfl⟩ := coord.surjective r
  obtain ⟨c, rfl⟩ := coord.surjective c
  rw [specialize_negative, Matrix.map_apply, fPolynomial_entry]
  rw [← coord_fin r, ← coord_fin c, fullMatrixMap_apply]
  have h := congrArg (ZMod.castHom (dvd_refl 2) (CoefficientField 0)) (table_negative i r c)
  simpa only [map_intCast, Int.coe_castRingHom] using h

end
end FullComparison

open FullComparison in
/-- The four binary tables are the actual Geck generators on all 52 coordinates. -/
public theorem ambientGenerator_fullMatrixComparison (i : Fin 4) :
    (ambientLeviHom (splitGenerator i)).val =
      AmbientComputation.fullMatrixMap AmbientComputation.basisEquiv
        (AmbientComputation.generator i) := by
  change (F4Chevalley.rootCurve (signedRoot i) (1 : CoefficientField 0)).val = _
  fin_cases i
  · exact (congrArg Units.val (rootCurveUnit_simple (node 0)
      (1 : CoefficientField 0))).trans (positive_comparison 0)
  · exact (congrArg Units.val (rootCurveUnit_simple (node 1)
      (1 : CoefficientField 0))).trans (positive_comparison 1)
  · exact (congrArg Units.val (rootCurveUnit_neg_simple (node 0)
      (1 : CoefficientField 0))).trans (negative_comparison 0)
  · exact (congrArg Units.val (rootCurveUnit_neg_simple (node 1)
      (1 : CoefficientField 0))).trans (negative_comparison 1)

end ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof
