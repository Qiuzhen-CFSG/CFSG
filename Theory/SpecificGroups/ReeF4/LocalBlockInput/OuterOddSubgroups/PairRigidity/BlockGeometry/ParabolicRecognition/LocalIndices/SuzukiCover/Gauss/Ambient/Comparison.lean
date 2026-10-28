module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Tables
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration

/-!
# Full parameter-dependent Geck generator comparison

The positive simple-root formulas are evaluated in the complete enumeration
of the four Cartan and 48 root coordinates. Integer root-table arithmetic
certifies every root-string coefficient. Separate kernel-checked tables for
the linear, quadratic and cubic coefficients identify the entire polynomial
curve over each Ree coefficient field. Omega conjugation gives the negative
curves. Consequently `simpleComparison` holds for every m and every parameter.

The integral coordinate argument is adapted from
`ParabolicAmalgam/BinaryLocals/SuzukiProjection/MatrixIdentification/Representation/Kernel/AmbientRelations/FullMatrixComparison.lean`.
Here the coefficients are checked separately, so the proof does not infer
an arbitrary-parameter identity from a binary specialization.
Source: `RootPairing.IntegralGeckConstruction`, GLS3 Table 2.4 type V and
2.3.8, `refs/KGroup/GLS3/chapter2.tex`.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open scoped Matrix
set_option linter.unusedSimpArgs false
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient
namespace ParameterComparison
noncomputable section
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
open Parabolics.BinarySuzuki.MatrixIdentification.KernelProof.AmbientComputation
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


lemma f_entry (i : Fin 2) (n : ℕ) (r c : Index) :
    fDividedPower (node i) n (coord r) (coord c) =
      eDividedPower (node i) n (coord (reverseIndex r)) (coord (reverseIndex c)) := by
  rw [fDividedPower, mul_omega_entry, omega_mul_entry, ← coord_reverse, ← coord_reverse]

lemma linear_table : ∀ (p : Bool) (i : Fin 2) (r c : Index),
    (eLinear i (if p then r else reverseIndex r)
      (if p then c else reverseIndex c) : ZMod 2) =
      incidence (linearSupport (simpleIndex p i)) (finSumFinEquiv r) (finSumFinEquiv c) := by
  decide +kernel

lemma quadratic_table : ∀ (p : Bool) (i : Fin 2) (r c : Index),
    (eHigher i 2 (if p then r else reverseIndex r)
      (if p then c else reverseIndex c) : ZMod 2) =
      incidence (quadraticSupport (simpleIndex p i)) (finSumFinEquiv r) (finSumFinEquiv c) := by
  decide +kernel

lemma cubic_table : ∀ (i : Fin 2) (r c : Index), (eHigher i 3 r c : ZMod 2) = 0 := by
  decide +kernel

lemma cubic_field (m : ℕ) (i : Fin 2) (r c : Index) :
    (eHigher i 3 r c : CoefficientField m) = 0 := by
  simpa only [map_intCast, map_zero] using
    congrArg (ZMod.castHom (dvd_refl 2) (CoefficientField m)) (cubic_table i r c)

lemma cast_incidence {m : ℕ} (s : List (Fin 52 × Fin 52)) (r c : Fin 52) :
    ZMod.castHom (dvd_refl 2) (CoefficientField m) (incidence (R := ZMod 2) s r c) =
      incidence s r c := by
  simp only [incidence]
  split_ifs <;> simp

lemma linear_field (m : ℕ) (p : Bool) (i : Fin 2) (r c : Index) :
    (eLinear i (if p then r else reverseIndex r)
      (if p then c else reverseIndex c) : CoefficientField m) =
      incidence (linearSupport (simpleIndex p i)) (finSumFinEquiv r) (finSumFinEquiv c) := by
  simpa only [map_intCast, cast_incidence] using
    congrArg (ZMod.castHom (dvd_refl 2) (CoefficientField m)) (linear_table p i r c)

lemma quadratic_field (m : ℕ) (p : Bool) (i : Fin 2) (r c : Index) :
    (eHigher i 2 (if p then r else reverseIndex r)
      (if p then c else reverseIndex c) : CoefficientField m) =
      incidence (quadraticSupport (simpleIndex p i)) (finSumFinEquiv r) (finSumFinEquiv c) := by
  simpa only [map_intCast, cast_incidence] using
    congrArg (ZMod.castHom (dvd_refl 2) (CoefficientField m)) (quadratic_table p i r c)

lemma fullMatrixEquiv_apply (m : ℕ)
    (M : Matrix (Fin 52) (Fin 52) (CoefficientField m)) (r c : Index) :
    fullMatrixEquiv m M (coord r) (coord c) = M (finSumFinEquiv r) (finSumFinEquiv c) := by
  rw [← coord_fin r, ← coord_fin c]
  simp [fullMatrixEquiv, Matrix.reindex_apply]

lemma positive_comparison (m : ℕ) (i : Fin 2) (t : CoefficientField m) :
    positiveMatrix (node i) t = fullMatrixEquiv m (simpleMatrix true i t) := by
  ext r c
  obtain ⟨r, rfl⟩ := coord.surjective r
  obtain ⟨c, rfl⟩ := coord.surjective c
  rw [fullMatrixEquiv_apply]
  simp only [positiveMatrix_formula, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    eDividedPower_one, eLinear_entry, eHigher_entry i 0, eHigher_entry i 1,
    Int.coe_castRingHom, show 1 + 2 = (3 : ℕ) from rfl, cubic_field, Int.cast_zero, smul_eq_mul, mul_zero, add_zero,
    simpleMatrix, Matrix.one_apply, Equiv.apply_eq_iff_eq]
  rw [show (eLinear i r c : CoefficientField m) = _ from linear_field m true i r c,
    show (eHigher i 2 r c : CoefficientField m) = _ from quadratic_field m true i r c]

lemma negative_comparison (m : ℕ) (i : Fin 2) (t : CoefficientField m) :
    negativeMatrix (node i) t = fullMatrixEquiv m (simpleMatrix false i t) := by
  ext r c
  obtain ⟨r, rfl⟩ := coord.surjective r
  obtain ⟨c, rfl⟩ := coord.surjective c
  rw [fullMatrixEquiv_apply]
  simp only [negativeMatrix_formula, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    f_entry, eDividedPower_one, eLinear_entry, eHigher_entry i 0, eHigher_entry i 1,
    Int.coe_castRingHom, show 1 + 2 = (3 : ℕ) from rfl, cubic_field, Int.cast_zero, smul_eq_mul, mul_zero, add_zero,
    simpleMatrix, Matrix.one_apply, Equiv.apply_eq_iff_eq]
  rw [show (eLinear i (reverseIndex r) (reverseIndex c) : CoefficientField m) = _ from
      linear_field m false i r c,
    show (eHigher i 2 (reverseIndex r) (reverseIndex c) : CoefficientField m) = _ from
      quadratic_field m false i r c]

end
end ParameterComparison

open ParameterComparison in
/-- The coefficient tables give the actual full simple-root matrices at every field parameter. -/
public theorem simpleComparison (m : ℕ) : SimpleComparison m := by
  intro p i t
  have hi : (if i = 0 then (1 : Fin 4) else 2) = nodeIndex i := by fin_cases i <;> rfl
  rw [hi]
  cases p
  · exact (congrArg Units.val (rootCurveUnit_neg_simple (node i) t)).trans
      (negative_comparison m i t)
  · exact (congrArg Units.val (rootCurveUnit_simple (node i) t)).trans
      (positive_comparison m i t)

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient
