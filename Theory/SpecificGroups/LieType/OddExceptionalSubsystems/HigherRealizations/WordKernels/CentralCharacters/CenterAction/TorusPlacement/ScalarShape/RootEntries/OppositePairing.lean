module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.RootEntries.Transport

/-!
# Opposite-root pairings in the literal E7 and E8 representations

On the Cartan-plus-root basis, the integral form has Cartan block
`-|cartanMatrix i j|`, zero mixed blocks, and opposite-root entries
`-(-1)^height`. Every simple root therefore pairs with its opposite to one.
The E7 and E8 roots all have squared norm two: a root sum and the corresponding
root difference cannot both be roots, so the raising coefficients on these
strings are one. Height parity and Cartan symmetry then make the positive
Geck operators skew-adjoint. The root-negating involution supplies the negative
operators.

The factorial identities transfer skew-adjointness to divided powers by
cancellation over the integers. After specialization, the transpose of a
literal curve acts on the form as the curve with negative parameter. The
additive curve law proves preservation over every commutative ring, without
field division, including characteristics two and three. `Transport` propagates
this identity through evaluated words and extracts reciprocal diagonal entries.
Thus the two final theorems discharge precisely the `hpair` premises of the
parent root-entry assembly, without centrality, finiteness, or an oddness premise.

Sources: the integral Chevalley construction underlying GLS3 §§1.12.5–6 and
§2.6.2 (`refs/KGroup/GLS3/Chapter1.tex` and `chapter2.tex`), used for the
higher subsystem embeddings in Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape

open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators
attribute [local instance] Classical.decEq
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace OppositePairing.Integral
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private def heightSign (r : ι) : ℤ := let := P.indexNeg; ((b.height r).negOnePow : ℤ)

private def integralForm : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  let := P.indexNeg
  Matrix.fromBlocks
    (fun i j => -|b.cartanMatrix i j|) 0 0
    (fun r s => if s = -r then -heightSign (P := P) (b := b) r else 0)

private lemma heightSign_neg (r : ι) : (let := P.indexNeg; heightSign (P := P) (b := b) (-r) = heightSign (P := P) (b := b) r) := by
  let := P.indexNeg
  change ((b.height (-r)).negOnePow : ℤ) = _
  rw [b.height_reflectionPerm_self]
  simp [heightSign]

private lemma heightSign_add {i : b.support} {j k : ι}
    (hk : P.root k = P.root j + P.root i) :
    heightSign (P := P) (b := b) k = - heightSign (P := P) (b := b) j := by
  let := P.indexNeg
  have hh := b.height_add hk
  rw [show b.height i = 1 from b.height_one_of_mem_support i.property] at hh
  unfold heightSign
  rw [hh, Int.negOnePow_add]
  norm_num


private lemma opp_opp (x : ι) : P.reflectionPerm (P.reflectionPerm x x) (P.reflectionPerm x x) = x := by
  apply P.root.injective
  rw [P.root_reflectionPerm, P.reflection_apply_self,
    P.root_reflectionPerm, P.reflection_apply_self]
  simp

private lemma opp_eq_iff (r c : ι) : P.reflectionPerm r r = c ↔ r = P.reflectionPerm c c := by
  constructor
  · intro h
    rw [← h, opp_opp]
  · intro h
    rw [h, opp_opp]

private lemma sum_reflect_eval (c : ι) (f : ι → ℤ) :
    (∑ a, if c = (P.reflectionPerm a) a then f a else 0) =
      f ((P.reflectionPerm c) c) := by
  classical
  have hh (a : ι) : c = P.reflectionPerm a a ↔ a = P.reflectionPerm c c := by
    rw [eq_comm, opp_eq_iff]
  simp only [hh]
  simp

private lemma heightSign_simple (i : b.support) : heightSign (P := P) (b := b) i = -1 := by
  simp [heightSign, b.height_one_of_mem_support i.property]

private lemma heightSign_opp (r : ι) : heightSign (P := P) (b := b) (P.reflectionPerm r r) = heightSign (P := P) (b := b) r := by
  exact heightSign_neg r

private lemma e_skew_of_coeff (i : b.support)
    (hsym : ∀ j k, b.cartanMatrix j k = b.cartanMatrix k j)
    (hcoeff : ∀ (j k : ι), P.root k = P.root j + P.root i →
      P.chainBotCoeff i j = 0) :
    (eMatrix (P := P) (b := b) i).transpose * integralForm + integralForm * eMatrix i = 0 := by
  let := P.indexNeg
  ext (r | r) (c | c)
  · simp [integralForm, Matrix.fromBlocks, eMatrix, heightSign, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type]
  · simp [integralForm, Matrix.fromBlocks, eMatrix, heightSign, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type]
    rw [sum_reflect_eval]
    simp only [ite_and]
    simp only [Finset.sum_ite_eq', Finset.mem_attach, ite_true]
    by_cases hc : c = P.reflectionPerm i i
    · subst c
      simp [opp_opp, heightSign, b.height_one_of_mem_support i.property, hsym r i]
    · have hh : P.reflectionPerm c c ≠ i := fun h => hc ((opp_eq_iff c i).mp h)
      simp [hc, hh]
  · simp [integralForm, Matrix.fromBlocks, eMatrix, heightSign, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type]
    simp only [ite_and]
    simp only [Finset.sum_ite_eq', Finset.mem_attach, ite_true]
    by_cases hr : r = P.reflectionPerm i i
    · subst r
      have hs : ((b.height (P.reflectionPerm i i)).negOnePow : ℤ) = -1 :=
        (heightSign_opp (b := b) i).trans (heightSign_simple i)
      simp [opp_opp, hs]
    · have hh : (i : ι) ≠ P.reflectionPerm r r := by
        intro h
        exact hr ((opp_eq_iff r i).mp h.symm)
      simp [hr, hh]
  · simp [integralForm, Matrix.fromBlocks, eMatrix, heightSign, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type]

    rw [sum_reflect_eval]
    have hswap (a : ι) (x : ℤ) :
        (if P.root a = P.root i + P.root c then
          if a = P.reflectionPerm r r then x else 0 else 0) =
        (if a = P.reflectionPerm r r then
          if P.root a = P.root i + P.root c then x else 0 else 0) := by
      split_ifs <;> rfl
    simp only [hswap, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have he : P.root (P.reflectionPerm c c) = P.root i + P.root r ↔
        P.root (P.reflectionPerm r r) = P.root i + P.root c := by
      simp only [P.root_reflectionPerm, P.reflection_apply_self]
      constructor
      · intro h
        calc
          -P.root r = P.root i - (P.root i + P.root r) := by abel
          _ = P.root i - -P.root c := by rw [← h]
          _ = _ := by simp
      · intro h
        calc
          -P.root c = P.root i - (P.root i + P.root c) := by abel
          _ = P.root i - -P.root r := by rw [← h]
          _ = _ := by simp
    by_cases hc : P.root (P.reflectionPerm c c) = P.root i + P.root r
    · have hr := he.mp hc
      have hcr := hcoeff r (P.reflectionPerm c c) (hc.trans (add_comm _ _))
      have hcc := hcoeff c (P.reflectionPerm r r) (hr.trans (add_comm _ _))
      have hs := heightSign_add (b := b) (hc.trans (add_comm _ _))
      simp only [heightSign] at hs
      simp [hc, hr, hcr, hcc, hs]
    · simp only [if_neg hc, if_neg (mt he.mpr hc), neg_zero, add_zero]

private lemma omega_selfadjoint :
    (omegaMatrix (P := P) (b := b)).transpose * integralForm = integralForm * omegaMatrix := by
  ext (r | r) (c | c)
  · simp [integralForm, omegaMatrix, Matrix.fromBlocks, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type, Matrix.one_apply]
  · simp [integralForm, omegaMatrix, Matrix.fromBlocks, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type, Matrix.one_apply]
  · simp [integralForm, omegaMatrix, Matrix.fromBlocks, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type, Matrix.one_apply]
  · simp [integralForm, omegaMatrix, Matrix.fromBlocks, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type, Matrix.one_apply]

    rw [sum_reflect_eval]
    by_cases h : P.reflectionPerm c c = P.reflectionPerm r r
    · have hc : c = r := by
        have hh := congrArg (fun x => P.reflectionPerm x x) h
        simpa only [opp_opp] using hh
      subst c
      simp [heightSign_opp]
    · simp [h]

private lemma f_skew_of_e (i : b.support)
    (h : (eMatrix (P := P) (b := b) i).transpose * integralForm = -(integralForm * eMatrix i)) :
    (fMatrix i).transpose * integralForm = -(integralForm * fMatrix i) := by
  have hf : fMatrix i = omegaMatrix * eMatrix i * omegaMatrix := by
    rw [omegaMatrix_mul_eMatrix, mul_assoc, omegaMatrix_sq, mul_one]
  rw [hf, Matrix.transpose_mul, Matrix.transpose_mul]
  calc
    omegaMatrix.transpose * ((eMatrix i).transpose * omegaMatrix.transpose) * integralForm =
        omegaMatrix.transpose * ((eMatrix i).transpose * (omegaMatrix.transpose * integralForm)) := by
          simp only [mul_assoc]
    _ = omegaMatrix.transpose * ((eMatrix i).transpose * (integralForm * omegaMatrix)) := by
      rw [omega_selfadjoint]
    _ = omegaMatrix.transpose * (-(integralForm * eMatrix i) * omegaMatrix) := by
      rw [← mul_assoc (eMatrix i).transpose integralForm omegaMatrix, h]
    _ = -(integralForm * (omegaMatrix * eMatrix i * omegaMatrix)) := by
      simp only [neg_mul, mul_neg, ← mul_assoc, omega_selfadjoint]

private lemma integralForm_opposite_simple (i : b.support) :
    (integralForm (P := P) (b := b)) (Sum.inr (P.reflectionPerm i i)) (Sum.inr (i : ι)) = 1 := by
  simp [integralForm, Matrix.fromBlocks, opp_opp, heightSign_opp, heightSign_simple]

end OppositePairing.Integral

namespace OppositePairing.Exponential
variable {n κ S : Type*} [Fintype n] [DecidableEq n] [CommRing S]
private lemma pow_adjoint (A B : Matrix n n ℤ) (h : A.transpose * B = -(B * A)) (k : ℕ) :
    (A ^ k).transpose * B = (-1 : ℤ) ^ k • (B * A ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.transpose_mul, mul_assoc, ih, Matrix.mul_smul,
      ← mul_assoc, h, neg_mul, mul_assoc, ← pow_succ]
    simp only [pow_succ, neg_smul, one_smul, smul_neg, mul_neg, mul_one]
    rw [← pow_succ', ← pow_succ]

private lemma divided_adjoint (D : IntegralCubicFamily κ n) (i : κ) (B : Matrix n n ℤ)
    (hf : ∀ a, D.dividedPower i 1 ^ a = a.factorial • D.dividedPower i a)
    (h : (D.dividedPower i 1).transpose * B = -(B * D.dividedPower i 1))
    (a : ℕ) :
    (D.dividedPower i a).transpose * B = (-1 : ℤ) ^ a • (B * D.dividedPower i a) := by
  have hh := pow_adjoint (D.dividedPower i 1) B h a
  rw [hf] at hh
  simp only [Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm] at hh
  rw [smul_comm] at hh
  ext x y
  exact nsmul_right_injective (Nat.factorial_ne_zero a) (congrFun₂ hh x y)

private lemma curve_preserves (D : IntegralCubicFamily κ n) (i : κ) (B : Matrix n n ℤ)
    (hf : ∀ a, D.dividedPower i 1 ^ a = a.factorial • D.dividedPower i a)
    (h : (D.dividedPower i 1).transpose * B = -(B * D.dividedPower i 1))
    (t : S) :
    (D.curve i t).transpose * B.map (Int.castRingHom S) * D.curve i t =
      B.map (Int.castRingHom S) := by
  have ha (a : ℕ) : (D.coefficient (S := S) i a).transpose * B.map (Int.castRingHom S) =
      (-1 : S) ^ a • (B.map (Int.castRingHom S) * D.coefficient i a) := by
    have hmap (z : ℤ) (C : Matrix n n ℤ) :
        (z • C).map (Int.castRingHom S) = (z : S) • C.map (Int.castRingHom S) := by
      ext x y
      exact Int.cast_mul z (C x y)
    simp only [IntegralCubicFamily.coefficient, ← Matrix.transpose_map, ← Matrix.map_mul,
      divided_adjoint D i B hf h, hmap, Int.cast_pow, Int.cast_neg, Int.cast_one]
  have hc : (D.curve i t).transpose * B.map (Int.castRingHom S) =
      B.map (Int.castRingHom S) * D.curve i (-t) := by
    simp only [IntegralCubicFamily.curve, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_smul, add_mul, one_mul, smul_mul_assoc, ha, mul_add,
      mul_one, mul_smul_comm, smul_smul]
    norm_num
    module
  rw [hc, mul_assoc, D.curve_neg_mul, mul_one]
end OppositePairing.Exponential


namespace OppositePairing.Coordinates
private lemma norm_two_not_sum_and_diff (i j k l : Vec 8)
    (hi : dot i i = 2) (hj : dot j j = 2) (hk : dot k k = 2) (hl : dot l l = 2)
    (hadd : k = j + i) (hsub : l = j - i) : False := by
  have he : dot k k + dot l l = 2 * dot j j + 2 * dot i i := by
    rw [hadd, hsub]
    simp only [dot, Pi.add_apply, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  linarith

private lemma e7_coeff (i j k : typeE7Roots)
    (hk : typeE7RootPairing.root k = typeE7RootPairing.root j + typeE7RootPairing.root i) :
    typeE7RootPairing.chainBotCoeff i j = 0 := by
  apply typeE7RootPairing.chainBotCoeff_eq_zero_iff.mpr
  right
  rintro ⟨l, hl⟩
  exact norm_two_not_sum_and_diff i.val j.val k.val l.val
    (typeE7Root_dot_self i) (typeE7Root_dot_self j)
    (typeE7Root_dot_self k) (typeE7Root_dot_self l)
    (congrArg (fun x : typeE7Space => x.val) hk)
    (congrArg (fun x : typeE7Space => x.val) hl)

private lemma e8_coeff (i j k : typeE8Roots)
    (hk : typeE8RootPairing.root k = typeE8RootPairing.root j + typeE8RootPairing.root i) :
    typeE8RootPairing.chainBotCoeff i j = 0 := by
  apply typeE8RootPairing.chainBotCoeff_eq_zero_iff.mpr
  right
  rintro ⟨l, hl⟩
  exact norm_two_not_sum_and_diff i.val j.val k.val l.val
    (typeE8Root_dot_self i) (typeE8Root_dot_self j)
    (typeE8Root_dot_self k) (typeE8Root_dot_self l) hk hl

private lemma e7_symm (i j : typeE7RootPairing_base.support) :
    typeE7RootPairing_base.cartanMatrix i j = typeE7RootPairing_base.cartanMatrix j i := by
  obtain ⟨i, rfl⟩ := typeE7RootPairing_baseEquiv.surjective i
  obtain ⟨j, rfl⟩ := typeE7RootPairing_baseEquiv.surjective j
  simp only [typeE7RootPairing_base_cartan_apply]
  fin_cases i <;> fin_cases j <;> rfl

private lemma e8_symm (i j : typeE8RootPairing_base.support) :
    typeE8RootPairing_base.cartanMatrix i j = typeE8RootPairing_base.cartanMatrix j i := by
  obtain ⟨i, rfl⟩ := typeE8RootPairing_baseEquiv.surjective i
  obtain ⟨j, rfl⟩ := typeE8RootPairing_baseEquiv.surjective j
  simp only [typeE8RootPairing_base_cartan_apply]
  fin_cases i <;> fin_cases j <;> rfl
end OppositePairing.Coordinates

namespace OppositePairing.Integral
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
private lemma simple_preserves {S : Type*} [CommRing S] (i : b.support)
    (hsym : ∀ j k, b.cartanMatrix j k = b.cartanMatrix k j)
    (hcoeff : ∀ (j k : ι), P.root k = P.root j + P.root i → P.chainBotCoeff i j = 0)
    (s : Bool) (t : S) :
    let C := (simpleFamily (b := b)).curve (s, i) t
    C.transpose * (integralForm (b := b)).map (Int.castRingHom S) * C =
      (integralForm (b := b)).map (Int.castRingHom S) := by
  apply OppositePairing.Exponential.curve_preserves
  · intro a
    cases s
    · simpa only [simpleFamily, fDividedPower_one] using fMatrix_pow_eq_factorial_smul i a
    · simpa only [simpleFamily, eDividedPower_one] using eMatrix_pow_eq_factorial_smul i a
  · have he := eq_neg_of_add_eq_zero_left (e_skew_of_coeff i hsym hcoeff)
    cases s
    · simpa only [simpleFamily, fDividedPower_one] using f_skew_of_e i he
    · simpa only [simpleFamily, eDividedPower_one] using he
end OppositePairing.Integral

local instance oppositePairing_fintypeE7 : Fintype typeE7Roots := Fintype.ofFinite _
local instance oppositePairing_fintypeE8 : Fintype typeE8Roots := Fintype.ofFinite _
/-- The integral height-sign pairing on the actual E7 Cartan-plus-root basis, specialized to `F`. -/
def e7OppositePairingForm (F : Type*) [CommRing F] :
    Matrix (typeE7RootPairing_base.support ⊕ typeE7Roots)
      (typeE7RootPairing_base.support ⊕ typeE7Roots) F :=
  (Matrix.fromBlocks
    (fun i j => -|typeE7RootPairing_base.cartanMatrix i j|) 0 0
    (fun r s => if s = typeE7RootPairing.reflectionPerm r r then
      -((typeE7RootPairing_base.height r).negOnePow : ℤ) else 0)).map (Int.castRingHom F)
/-- The corresponding pairing on the actual E8 Cartan-plus-root basis. -/
def e8OppositePairingForm (F : Type*) [CommRing F] :
    Matrix (typeE8RootPairing_base.support ⊕ typeE8Roots)
      (typeE8RootPairing_base.support ⊕ typeE8Roots) F :=
  (Matrix.fromBlocks
    (fun i j => -|typeE8RootPairing_base.cartanMatrix i j|) 0 0
    (fun r s => if s = typeE8RootPairing.reflectionPerm r r then
      -((typeE8RootPairing_base.height r).negOnePow : ℤ) else 0)).map (Int.castRingHom F)
/-- Every literal signed E7 simple curve preserves the constructed form. -/
theorem e7_simple_preserves_oppositePairingForm (F : Type*) [CommRing F] (s : Bool)
    (i : typeE7RootPairing_base.support) (t : F) :
    let A := (simpleFamily (b := typeE7RootPairing_base)).curve (s, i) t
    A.transpose * e7OppositePairingForm F * A = e7OppositePairingForm F := by
  exact OppositePairing.Integral.simple_preserves i OppositePairing.Coordinates.e7_symm
    (OppositePairing.Coordinates.e7_coeff i) s t
/-- Every literal signed E8 simple curve preserves the constructed form. -/
theorem e8_simple_preserves_oppositePairingForm (F : Type*) [CommRing F] (s : Bool)
    (i : typeE8RootPairing_base.support) (t : F) :
    let A := (simpleFamily (b := typeE8RootPairing_base)).curve (s, i) t
    A.transpose * e8OppositePairingForm F * A = e8OppositePairingForm F := by
  exact OppositePairing.Integral.simple_preserves i OppositePairing.Coordinates.e8_symm
    (OppositePairing.Coordinates.e8_coeff i) s t
/-- A diagonal evaluated six-node word has reciprocal entries on the extra E7 root and its opposite. -/
theorem e7Six_diagonal_extra_pair (F : Type*) [Field F] (w : SixNodeWord F)
    (hd : (e7Six F w).val.val.IsDiag) :
    let r : typeE7Roots := typeE7RootPairing_baseEquiv 6
    (e7Six F w).val.val
      (Sum.inr (typeE7RootPairing.reflectionPerm r r))
      (Sum.inr (typeE7RootPairing.reflectionPerm r r)) *
      (e7Six F w).val.val (Sum.inr r) (Sum.inr r) = 1 := by
  apply e7Six_diagonal_extra_pair_of_form F w hd (e7OppositePairingForm F)
  · change ((OppositePairing.Integral.integralForm (b := typeE7RootPairing_base))
      (Sum.inr (typeE7RootPairing.reflectionPerm (typeE7RootPairing_baseEquiv 6)
        (typeE7RootPairing_baseEquiv 6)))
      (Sum.inr (typeE7RootPairing_baseEquiv 6)) : F) ≠ 0
    rw [OppositePairing.Integral.integralForm_opposite_simple]
    norm_num
  · intro s i t
    exact e7_simple_preserves_oppositePairingForm F s (e7Node i) t
/-- A diagonal evaluated six-node word has reciprocal entries on the extra E8 root and its opposite. -/
theorem e8Six_diagonal_extra_pair (F : Type*) [Field F] (w : SixNodeWord F)
    (hd : (e8Six F w).val.val.IsDiag) :
    let r : typeE8Roots := typeE8RootPairing_baseEquiv 6
    (e8Six F w).val.val
      (Sum.inr (typeE8RootPairing.reflectionPerm r r))
      (Sum.inr (typeE8RootPairing.reflectionPerm r r)) *
      (e8Six F w).val.val (Sum.inr r) (Sum.inr r) = 1 := by
  apply e8Six_diagonal_extra_pair_of_form F w hd (e8OppositePairingForm F)
  · change ((OppositePairing.Integral.integralForm (b := typeE8RootPairing_base))
      (Sum.inr (typeE8RootPairing.reflectionPerm (typeE8RootPairing_baseEquiv 6)
        (typeE8RootPairing_baseEquiv 6)))
      (Sum.inr (typeE8RootPairing_baseEquiv 6)) : F) ≠ 0
    rw [OppositePairing.Integral.integralForm_opposite_simple]
    norm_num
  · intro s i t
    exact e8_simple_preserves_oppositePairingForm F s (e8Node i) t

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape
