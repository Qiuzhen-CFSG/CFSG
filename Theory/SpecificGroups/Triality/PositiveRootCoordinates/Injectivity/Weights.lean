module
public import Theory.AlgebraicGroup.RootSystems.IntegralAllRootOperators

/-!
# Weight support of the canonical integral root operators

Geck's lattice has weight zero on the Cartan basis and the corresponding root
on each root basis vector. Simple operators raise this weight by their simple
root. The chosen integral Tits word transports weights by its actual Weyl
transformation, so the canonical operator on a positive root raises weights by
that root. The factorial identity gives the same assertion for every divided
power over the integers, before any reduction of scalars.

These support statements supply the filtration used for uniqueness of the
positive D4 product (GLS3, 1.12.7 and 2.3.6–7).
-/

@[expose] public section
open scoped BigOperators
namespace Triality.Standard.PositiveCoordinates.Injectivity
noncomputable section

section Matrices
variable {I W S : Type*} [Fintype I] [DecidableEq I] [AddCommGroup W] [CommRing S]
  (w : I → W)

def Homogeneous (A : Matrix I I S) (a : W) : Prop :=
  ∀ i j, A i j ≠ 0 → w i = a + w j

omit [Fintype I] in
lemma homogeneous_one : Homogeneous w (1 : Matrix I I S) 0 := by
  intro i j h
  by_cases hij : i = j
  · subst j; simp
  · exact False.elim (h (by simp [hij]))

omit [DecidableEq I] in
lemma homogeneous_mul {A B : Matrix I I S} {a b : W}
    (hA : Homogeneous w A a) (hB : Homogeneous w B b) :
    Homogeneous w (A * B) (a + b) := by
  intro i j h
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hA' := hA i k (left_ne_zero_of_mul hk)
  have hB' := hB k j (right_ne_zero_of_mul hk)
  rw [hA', hB', add_assoc]

lemma homogeneous_pow {A : Matrix I I S} {a : W}
    (hA : Homogeneous w A a) (n : ℕ) :
    Homogeneous w (A ^ n) (n • a) := by
  induction n with
  | zero => simpa using homogeneous_one w
  | succ n ih => simpa [pow_succ, succ_nsmul] using homogeneous_mul w ih hA

/-- Support of a matrix transporting weights by a permutation. -/
def Transports (A : Matrix I I S) (g : W ≃ W) : Prop :=
  ∀ i j, A i j ≠ 0 → w i = g (w j)

omit [AddCommGroup W] in
lemma transports_inv {A B : Matrix I I S} (g : W ≃ W)
    (hA : Transports w A g) (hAB : A * B = 1) (hBA : B * A = 1) :
    Transports w B g.symm := by
  classical
  intro i j hij
  let D : Matrix I I S := Matrix.diagonal fun k => if w k = w i then 1 else 0
  let E : Matrix I I S := Matrix.diagonal fun k => if w k = g (w i) then 1 else 0
  have hAD : A * D = E * A := by
    ext k l
    simp only [D, E, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hkl : A k l = 0
    · simp [hkl]
    · have hk := hA k l hkl
      simp only [hk, g.injective.eq_iff]
      split_ifs <;> simp
  have hDB : D * B = B * E := by
    calc
      D * B = (B * A) * D * B := by rw [hBA, one_mul]
      _ = B * (A * D) * B := by simp only [Matrix.mul_assoc]
      _ = B * (E * A) * B := by rw [hAD]
      _ = B * E * (A * B) := by simp only [Matrix.mul_assoc]
      _ = B * E := by rw [hAB, mul_one]
  have he := congrFun (congrFun hDB i) j
  simp only [D, E, Matrix.diagonal_mul, Matrix.mul_diagonal, ite_true, one_mul] at he
  by_cases hj : w j = g (w i)
  · exact (g.symm_apply_eq.mpr hj).symm
  · simp only [if_neg hj, mul_zero] at he
    exact False.elim (hij he)

omit [DecidableEq I] in
lemma homogeneous_conjugate {A T U : Matrix I I S} {a : W} (g : W ≃+ W)
    (hA : Homogeneous w A a) (hT : Transports w T g.toEquiv)
    (hU : Transports w U g.symm.toEquiv) :
    Homogeneous w (T * A * U) (g a) := by
  intro i j hij
  obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hl)
  have hi := hT i k (left_ne_zero_of_mul hk)
  have hk' := hA k l (right_ne_zero_of_mul hk)
  have hl' := hU l j (right_ne_zero_of_mul hl)
  change w i = g (w k) at hi
  change w l = g.symm (w j) at hl'
  rw [hi, hk', map_add]
  change g a + g (w l) = _
  rw [hl', g.apply_symm_apply]

end Matrices

section Roots
open RootPairing.IntegralGeckConstruction
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

def rootWeight : b.support ⊕ ι → M := Sum.elim (fun _ => 0) P.root

omit [P.IsReduced] in
lemma eMatrix_homogeneous (i : b.support) :
    Homogeneous (rootWeight (b := b)) (eMatrix i) (P.root i) := by
  classical
  let := P.indexNeg
  intro j k hjk
  rcases j with j | j <;> rcases k with k | k
  · simp [eMatrix] at hjk
  · have h : j = i ∧ k = -i := by
      by_contra h
      apply hjk
      change (if j = i ∧ k = -i then 1 else 0) = 0
      rw [if_neg h]
    simp [rootWeight, h.2]
  · have h : j = i := by
      by_contra h
      exact hjk (by simp [eMatrix, h])
    simp [rootWeight, h]
  · have h : P.root j = P.root i + P.root k := by
      by_contra h
      exact hjk (by simp [eMatrix, h])
    exact h

lemma titsLift_transports (i : b.support) :
    Transports (rootWeight (b := b)) (titsLift i)
      (P.reflection i).toAddEquiv.toEquiv := by
  classical
  intro j k hjk
  rcases k with k | k
  · have hc := congrFun (titsLift_mulVec_u (P := P) i k) j
    simp only [u, Matrix.mulVec_single_one, Matrix.col_apply] at hc
    rcases j with j | j
    · simp [rootWeight]
    · have hz : titsLift i (Sum.inr j) (Sum.inl k) = 0 := by
        simpa [Pi.single_apply] using hc
      exact False.elim (hjk hz)
  · have hc := congrFun (titsLift_mulVec_v (P := P) i k) j
    simp only [v, Matrix.mulVec_single_one, Matrix.col_apply] at hc
    have hj : j = Sum.inr (P.reflectionPerm i k) := by
      by_contra h
      exact hjk (by simpa [Pi.single_apply, h] using hc)
    subst j
    exact P.root_reflectionPerm i k

lemma titsWord_transports (word : List b.support) :
    Transports (rootWeight (b := b)) (titsWord word)
      (RootPairing.Equiv.weightHom P (b.wordProd word)).toAddEquiv.toEquiv := by
  classical
  intro i j hij
  change rootWeight i = b.wordProd word • rootWeight j
  induction word generalizing i j with
  | nil =>
      have h : i = j := by
        by_contra h
        exact hij (by simp [titsWord, h])
      subst j
      simp
  | cons k word ih =>
      obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
      have hi := titsLift_transports k i l (left_ne_zero_of_mul hl)
      have hj := ih l j (right_ne_zero_of_mul hl)
      change rootWeight i = (P.reflection k) (rootWeight l) at hi
      rw [hi, hj, b.wordProd_cons, mul_smul]
      rfl

lemma rootOperator_homogeneous (r : ι) (hr : b.IsPos r) :
    Homogeneous (rootWeight (b := b)) (rootOperator r) (P.root r) := by
  let route := rootRoute (P := P) (b := b) r
  let g := (RootPairing.Equiv.weightHom P (b.wordProd route.word)).toAddEquiv
  have hT := titsWord_transports (P := P) route.word
  have hU := transports_inv (rootWeight (b := b)) g.toEquiv hT
    (titsWord_mul_inv route.word) (titsWord_inv_mul route.word)
  have h := homogeneous_conjugate (rootWeight (b := b)) g
    (eMatrix_homogeneous route.simple) hT hU
  have ht : g (P.root route.simple) = P.root r := by
    change b.wordProd route.word • P.root route.simple = P.root r
    rw [← root_reflectionWord, route.target]
  rw [ht] at h
  simpa only [rootOperator_of_pos r hr, transportedMatrix] using h

lemma rootDividedPower_homogeneous (r : ι) (hr : b.IsPos r) (n : ℕ) :
    Homogeneous (rootWeight (b := b)) (rootDividedPower r n) (n • P.root r) := by
  have h := homogeneous_pow (rootWeight (b := b)) (rootOperator_homogeneous r hr) n
  intro i j hij
  apply h i j
  rw [rootOperator_pow_eq_factorial_smul]
  change (n.factorial : ℤ) * rootDividedPower r n i j ≠ 0
  exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) hij

end Roots

end
end Triality.Standard.PositiveCoordinates.Injectivity
