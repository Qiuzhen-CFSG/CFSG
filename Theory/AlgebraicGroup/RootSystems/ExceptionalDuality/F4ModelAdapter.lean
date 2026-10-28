module

public import Theory.AlgebraicGroup.RootSystems.ExceptionalDuality.Core
public meta import Theory.AlgebraicGroup.RootSystems.Exceptional

/-!
# Type F4 exceptional-duality model adapter

This module transports the finite standard `F₄` matrix and positive-root
fingerprint calculations to an arbitrary finite reduced crystallographic real
root pairing whose chosen base has the standard `F₄` Cartan matrix.  Its
principal theorem says that two positive root-duality permutations on a
classified type `F₄` pairing are equal.

The proof enumerates all roots from the 24 checked positive coefficient rows by
induction under simple reflections.  An invariant positive form computes the
two possible root lengths and rules out the identity action on the numbered
base; the exported standard-matrix rigidity check then fixes the action there
as reversal.  Coxeter-product preservation determines the checked fingerprint
of every positive image, so `typeF4_positive_fingerprint_injective` identifies
the images.  Root-index negation handles the negative roots.  These finite
calculations also show that every root has one of the two simple-root lengths,
which yields the long-or-short exhaustiveness theorem below.  They provide the
type `F₄` uniqueness branch required by exceptional graph-field duality; the
classification and Cartan conventions are those of the repository's finite
root-system classification modules.
-/

namespace Theory.AlgebraicGroup

open Set
open StandardRootSystem

private def f4ReflectCoeffs (i : Fin 24) (j k : Fin 4) : ℤ :=
  typeF4PositiveCoeffs i k -
    (if k = j then ∑ l, typeF4PositiveCoeffs i l * typeF4CartanMatrix l j else 0)

set_option maxHeartbeats 800000 in
private lemma f4ReflectCoeffs_mem :
    ∀ (i : Fin 24) (j : Fin 4), ∃ i' : Fin 24,
      (∀ k, f4ReflectCoeffs i j k = typeF4PositiveCoeffs i' k) ∨
      (∀ k, f4ReflectCoeffs i j k = -typeF4PositiveCoeffs i' k) := by
  decide

set_option maxHeartbeats 800000 in
private lemma f4_simple_coeff :
    ∀ j : Fin 4, ∃ i : Fin 24, ∀ k,
      typeF4PositiveCoeffs i k = if k = j then 1 else 0 := by
  decide

set_option maxHeartbeats 800000 in
private lemma f4_positive_coeff_nonzero :
    ∀ i : Fin 24, ∃ k, 0 < typeF4PositiveCoeffs i k := by
  decide

private def f4ForwardPairing (i : Fin 24) (j : Fin 4) : ℤ :=
  ∑ k, typeF4PositiveCoeffs i k * typeF4CartanMatrix k j

private def f4BaseRootLength (i : Fin 4) : ℤ :=
  if i.val < 2 then 2 else 1

private def f4RootLengthTwice (i : Fin 24) : ℤ :=
  ∑ j, ∑ k,
    typeF4PositiveCoeffs i j * typeF4PositiveCoeffs i k *
      typeF4CartanMatrix k j * f4BaseRootLength j

private def f4RootLength (i : Fin 24) : ℤ :=
  f4RootLengthTwice i / 2

private def f4CoxeterFingerprint (i : Fin 24) (j : Fin 4) : ℤ :=
  f4ForwardPairing i j ^ 2 * f4BaseRootLength j / f4RootLength i

set_option maxHeartbeats 800000 in
private lemma f4RootLength_spec :
    ∀ i : Fin 24,
      f4RootLengthTwice i = 2 * f4RootLength i ∧ 0 < f4RootLength i := by
  decide

set_option maxHeartbeats 800000 in
private lemma f4CoxeterFingerprint_spec :
    ∀ i : Fin 24, ∀ j : Fin 4,
      f4RootLength i * f4CoxeterFingerprint i j =
        f4ForwardPairing i j ^ 2 * f4BaseRootLength j := by
  decide

set_option maxHeartbeats 800000 in
private lemma f4CoxeterFingerprint_abs_fingerprint :
    ∀ i j : Fin 24,
      (∀ k : Fin 4, f4CoxeterFingerprint i k = f4CoxeterFingerprint j k) →
      ∀ k : Fin 4, |f4ForwardPairing i k| = |f4ForwardPairing j k| := by
  decide

private noncomputable def f4RootCombination
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    (numbering : Fin 4 → ι)
    (c : Fin 4 → ℤ) : M :=
  ∑ k, (c k : ℝ) • P.root (numbering k)

private lemma f4RootCombination_reflect
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    (numbering : Fin 4 → ι)
    (c : Fin 4 → ℤ) (j : Fin 4) (q : ℤ) :
    f4RootCombination P numbering c -
        (q : ℝ) • P.root (numbering j) =
      f4RootCombination P numbering
        (fun k => c k - if k = j then q else 0) := by
  classical
  simp only [f4RootCombination, Int.cast_sub, Int.cast_ite, Int.cast_zero,
    sub_smul, Finset.sum_sub_distrib]
  simp

private lemma f4RootCombination_pairingIn
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic]
    (numbering : Fin 4 → ι)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering i) (numbering j) =
      typeF4CartanMatrix i j)
    { α : ι} {c : Fin 4 → ℤ}
    (hroot : P.root α = f4RootCombination P numbering c)
    (j : Fin 4) :
    P.pairingIn ℤ α (numbering j) =
      ∑ k, c k * typeF4CartanMatrix k j := by
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℝ))
  change algebraMap ℤ ℝ (P.pairingIn ℤ α (numbering j)) = _
  rw [P.algebraMap_pairingIn]
  push_cast
  rw [← P.root_coroot_eq_pairing, hroot]
  simp only [f4RootCombination, map_sum, LinearMap.coe_sum,
    Finset.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    P.root_coroot_eq_pairing]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact (P.algebraMap_pairingIn ℤ (numbering k) (numbering j)).symm.trans
    (congrArg (algebraMap ℤ ℝ) (hCartan k j))

private def IsF4RootCombination
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    (numbering : Fin 4 → ι) (α : ι) : Prop :=
  ∃ i : Fin 24,
    P.root α = f4RootCombination P numbering (typeF4PositiveCoeffs i) ∨
    P.root α = -f4RootCombination P numbering (typeF4PositiveCoeffs i)

private lemma isF4RootCombination_all
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (numbering : base.support ≃ Fin 4)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
      typeF4CartanMatrix i j) :
    ∀ α, IsF4RootCombination P (fun k => (numbering.symm k : ι)) α := by
  classical
  let := P.indexNeg
  let simple : Fin 4 → ι := fun k => numbering.symm k
  have hCartan' : ∀ i j, P.pairingIn ℤ (simple i) (simple j) =
      typeF4CartanMatrix i j := by
    simpa [simple] using hCartan
  change ∀ α, IsF4RootCombination P simple α
  intro α
  apply base.induction_reflect α
  · intro i hi
    obtain ⟨r, hir | hir⟩ := hi
    · refine ⟨r, Or.inr ?_⟩
      simpa using congrArg Neg.neg hir
    · refine ⟨r, Or.inl ?_⟩
      simpa using congrArg Neg.neg hir
  · intro i hi
    let j : Fin 4 := numbering ⟨i, hi⟩
    obtain ⟨r, hr⟩ := f4_simple_coeff j
    refine ⟨r, Or.inl ?_⟩
    have hij : numbering.symm j = ⟨i, hi⟩ := by simp [j]
    rw [show i = simple j by simpa [simple] using (congrArg Subtype.val hij).symm]
    simp only [f4RootCombination]
    simp_rw [hr]
    simp
  · intro i j hi hj
    let q : Fin 4 := numbering ⟨j, hj⟩
    have hjq : simple q = j := by simp [simple, q]
    obtain ⟨r, hir | hir⟩ := hi
    · have hp := f4RootCombination_pairingIn (P := P) simple hCartan' hir q
      obtain ⟨r', hr'⟩ := f4ReflectCoeffs_mem r q
      have hreflect :
          P.root (P.reflectionPerm j i) =
            f4RootCombination P simple (f4ReflectCoeffs r q) := by
        calc
          P.root (P.reflectionPerm j i) = P.reflection j (P.root i) :=
            P.root_reflectionPerm j i
          _ = P.root i - (P.pairingIn ℤ i j : ℝ) • P.root j := by
            rw [P.reflection_apply_root]
            congr 2
            exact (P.algebraMap_pairingIn ℤ i j).symm
          _ = f4RootCombination P simple (typeF4PositiveCoeffs r) -
              ((∑ k, typeF4PositiveCoeffs r k * typeF4CartanMatrix k q : ℤ) : ℝ) •
                P.root (simple q) := by rw [hir, ← hjq, hp]
          _ = f4RootCombination P simple (f4ReflectCoeffs r q) := by
            exact f4RootCombination_reflect simple
              (typeF4PositiveCoeffs r) q _
      rcases hr' with hr' | hr'
      · exact ⟨r', Or.inl (hreflect.trans (by
          congr 1
          funext k
          exact hr' k))⟩
      · refine ⟨r', Or.inr ?_⟩
        rw [hreflect]
        rw [show f4ReflectCoeffs r q = -typeF4PositiveCoeffs r' by
          funext k; exact hr' k]
        simp [f4RootCombination]
    · have hir' : P.root i =
          f4RootCombination P simple (-typeF4PositiveCoeffs r) := by
        rw [hir]
        simp [f4RootCombination]
      have hp' := f4RootCombination_pairingIn (P := P) simple hCartan' hir' q
      have hp : P.pairingIn ℤ i (simple q) =
          -∑ k, typeF4PositiveCoeffs r k * typeF4CartanMatrix k q := by
        simpa using hp'
      obtain ⟨r', hr'⟩ := f4ReflectCoeffs_mem r q
      have hreflect :
          P.root (P.reflectionPerm j i) =
            -f4RootCombination P simple (f4ReflectCoeffs r q) := by
        calc
          P.root (P.reflectionPerm j i) = P.reflection j (P.root i) :=
            P.root_reflectionPerm j i
          _ = P.root i - (P.pairingIn ℤ i j : ℝ) • P.root j := by
            rw [P.reflection_apply_root]
            congr 2
            exact (P.algebraMap_pairingIn ℤ i j).symm
          _ = -(f4RootCombination P simple (typeF4PositiveCoeffs r) -
              ((∑ k, typeF4PositiveCoeffs r k * typeF4CartanMatrix k q : ℤ) : ℝ) •
                P.root (simple q)) := by rw [hir, ← hjq, hp]; module
          _ = -f4RootCombination P simple (f4ReflectCoeffs r q) := by
            exact congrArg Neg.neg (f4RootCombination_reflect simple
              (typeF4PositiveCoeffs r) q _)
      rcases hr' with hr' | hr'
      · refine ⟨r', Or.inr ?_⟩
        rw [hreflect]
        congr 2
        funext k
        exact hr' k
      · refine ⟨r', Or.inl ?_⟩
        rw [hreflect]
        rw [show f4ReflectCoeffs r q = -typeF4PositiveCoeffs r' by
          funext k; exact hr' k]
        simp [f4RootCombination]

private lemma f4PositiveRoot_exists_combination
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (numbering : base.support ≃ Fin 4)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
      typeF4CartanMatrix i j)
    {α : ι} (hα : base.IsPos α) :
    ∃ i : Fin 24,
      P.root α = f4RootCombination P (fun k => (numbering.symm k : ι))
        (typeF4PositiveCoeffs i) := by
  classical
  obtain ⟨i, hi | hi⟩ := isF4RootCombination_all base numbering hCartan α
  · exact ⟨i, hi⟩
  · obtain ⟨k, hk⟩ := f4_positive_coeff_nonzero i
    have hn := base.isPos_repr_nonneg α hα (numbering.symm k)
    rw [hi] at hn
    simp only [map_neg, f4RootCombination, map_sum, map_smul,
      base.toWeightBasis_repr_root] at hn
    have hsum :
        (∑ c : Fin 4, (typeF4PositiveCoeffs i c : ℝ) •
            Finsupp.single (numbering.symm c) 1) (numbering.symm k) =
          (typeF4PositiveCoeffs i k : ℝ) := by
      change (∑ c : Fin 4,
        ((typeF4PositiveCoeffs i c : ℝ) •
          Finsupp.single (numbering.symm c) 1) (numbering.symm k)) = _
      rw [Finset.sum_eq_single k]
      · simp
      · intro c _ hck
        simp only [Finsupp.smul_apply]
        have hne : numbering.symm k ≠ numbering.symm c := fun h =>
          hck (numbering.symm.injective h.symm)
        rw [Finsupp.single_eq_of_ne hne]
        simp
      · simp
    change 0 ≤ -((∑ c : Fin 4, (typeF4PositiveCoeffs i c : ℝ) •
      Finsupp.single (numbering.symm c) 1) (numbering.symm k)) at hn
    rw [hsum] at hn
    have hk' : (0 : ℝ) < typeF4PositiveCoeffs i k := by exact_mod_cast hk
    linarith

public theorem exceptional_f4_positive_fingerprint_injective
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (numbering : base.support ≃ Fin 4)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
      typeF4CartanMatrix i j)
    {α β : ι} (hα : base.IsPos α) (hβ : base.IsPos β)
    (hfp : ∀ j : Fin 4,
      |P.pairingIn ℤ α (numbering.symm j)| =
        |P.pairingIn ℤ β (numbering.symm j)|) :
    α = β := by
  let simple : Fin 4 → ι := fun k => numbering.symm k
  have hCartan' : ∀ i j, P.pairingIn ℤ (simple i) (simple j) =
      typeF4CartanMatrix i j := by
    simpa [simple] using hCartan
  obtain ⟨i, hi⟩ := f4PositiveRoot_exists_combination base numbering hCartan hα
  obtain ⟨j, hj⟩ := f4PositiveRoot_exists_combination base numbering hCartan hβ
  have hipair (k : Fin 4) :
      P.pairingIn ℤ α (simple k) = f4ForwardPairing i k := by
    exact f4RootCombination_pairingIn simple hCartan' hi k
  have hjpair (k : Fin 4) :
      P.pairingIn ℤ β (simple k) = f4ForwardPairing j k := by
    exact f4RootCombination_pairingIn simple hCartan' hj k
  have hij : i = j := typeF4_positive_fingerprint_injective i j (by
    intro k
    rw [exceptionalAbsoluteCartanFingerprint_apply,
      exceptionalAbsoluteCartanFingerprint_apply]
    change |f4ForwardPairing i k| = |f4ForwardPairing j k|
    rw [← hipair, ← hjpair]
    exact hfp k)
  apply P.root.injective
  rw [hi, hj, hij]

private lemma f4SimpleRoot_length
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (B : P.InvariantForm) (numbering : Fin 4 → ι)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering i) (numbering j) =
      typeF4CartanMatrix i j) (i : Fin 4) :
    B.form (P.root (numbering i)) (P.root (numbering i)) =
      (f4BaseRootLength i : ℝ) *
        B.form (P.root (numbering 2)) (P.root (numbering 2)) := by
  have h01 := B.pairing_mul_eq_pairing_mul_swap (numbering 0) (numbering 1)
  have h12 := B.pairing_mul_eq_pairing_mul_swap (numbering 1) (numbering 2)
  have h23 := B.pairing_mul_eq_pairing_mul_swap (numbering 2) (numbering 3)
  simp only [← P.algebraMap_pairingIn ℤ] at h01 h12 h23
  rw [hCartan, hCartan] at h01 h12 h23
  norm_num [typeF4CartanMatrix] at h01 h12 h23
  simp at h01 h12 h23
  fin_cases i <;> simp [f4BaseRootLength] <;> linarith

private lemma f4RootCombination_length_twice
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (B : P.InvariantForm) (numbering : Fin 4 → ι)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering i) (numbering j) =
      typeF4CartanMatrix i j)
    (hbase : ∀ i,
      B.form (P.root (numbering i)) (P.root (numbering i)) =
        (f4BaseRootLength i : ℝ) *
          B.form (P.root (numbering 2)) (P.root (numbering 2)))
    (i : Fin 24) :
    2 * B.form
        (f4RootCombination P numbering (typeF4PositiveCoeffs i))
        (f4RootCombination P numbering (typeF4PositiveCoeffs i)) =
      (f4RootLengthTwice i : ℝ) *
        B.form (P.root (numbering 2)) (P.root (numbering 2)) := by
  let t := B.form (P.root (numbering 2)) (P.root (numbering 2))
  have hgram (j k : Fin 4) :
      2 * B.form (P.root (numbering j)) (P.root (numbering k)) =
        ((typeF4CartanMatrix j k * f4BaseRootLength k : ℤ) : ℝ) * t := by
    rw [B.two_mul_apply_root_root]
    rw [← P.algebraMap_pairingIn ℤ, hCartan, hbase]
    have hcast : algebraMap ℤ ℝ (typeF4CartanMatrix j k) =
        (typeF4CartanMatrix j k : ℝ) := by norm_num
    rw [hcast, Int.cast_mul]
    dsimp [t]
    ring
  calc
    2 * B.form
        (f4RootCombination P numbering (typeF4PositiveCoeffs i))
        (f4RootCombination P numbering (typeF4PositiveCoeffs i)) =
      ∑ j, ∑ k,
        (typeF4PositiveCoeffs i j : ℝ) *
          (typeF4PositiveCoeffs i k : ℝ) *
            (2 * B.form (P.root (numbering k)) (P.root (numbering j))) := by
      simp only [f4RootCombination, map_sum, LinearMap.coe_sum,
        Finset.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ j, ∑ k,
        (typeF4PositiveCoeffs i j : ℝ) *
          (typeF4PositiveCoeffs i k : ℝ) *
            (((typeF4CartanMatrix k j * f4BaseRootLength j : ℤ) : ℝ) * t) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [hgram k j]
    _ = (f4RootLengthTwice i : ℝ) * t := by
      simp only [f4RootLengthTwice]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

private lemma f4PositiveRoot_length
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (B : P.InvariantForm) (numbering : Fin 4 → ι)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering i) (numbering j) =
      typeF4CartanMatrix i j)
    {α : ι} (i : Fin 24)
    (hi : P.root α =
      f4RootCombination P numbering (typeF4PositiveCoeffs i)) :
    B.form (P.root α) (P.root α) =
      (f4RootLength i : ℝ) *
        B.form (P.root (numbering 2)) (P.root (numbering 2)) := by
  have htwice := f4RootCombination_length_twice B numbering hCartan
    (f4SimpleRoot_length B numbering hCartan) i
  rw [← hi] at htwice
  have hspec := (f4RootLength_spec i).1
  have hspec' : (f4RootLengthTwice i : ℝ) =
      2 * (f4RootLength i : ℝ) := by exact_mod_cast hspec
  rw [hspec'] at htwice
  linarith

private lemma f4PositiveRoot_coxeterFingerprint
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (B : P.InvariantForm) (numbering : Fin 4 → ι)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering i) (numbering j) =
      typeF4CartanMatrix i j)
    {α : ι} (i : Fin 24)
    (hi : P.root α =
      f4RootCombination P numbering (typeF4PositiveCoeffs i))
    (k : Fin 4) :
    P.pairingIn ℤ α (numbering k) * P.pairingIn ℤ (numbering k) α =
      f4CoxeterFingerprint i k := by
  let t := B.form (P.root (numbering 2)) (P.root (numbering 2))
  have ht : t ≠ 0 := B.ne_zero (numbering 2)
  have hlen := f4PositiveRoot_length B numbering hCartan i hi
  have hbase := f4SimpleRoot_length B numbering hCartan k
  have hrel := B.pairing_mul_eq_pairing_mul_swap α (numbering k)
  simp only [← P.algebraMap_pairingIn ℤ] at hrel
  rw [hlen, hbase] at hrel
  have hcancel :
      algebraMap ℤ ℝ (P.pairingIn ℤ (numbering k) α) *
          (f4RootLength i : ℝ) =
        algebraMap ℤ ℝ (P.pairingIn ℤ α (numbering k)) *
          (f4BaseRootLength k : ℝ) := by
    apply mul_right_cancel₀ ht
    simpa only [mul_assoc, t] using hrel
  rw [show algebraMap ℤ ℝ (P.pairingIn ℤ (numbering k) α) =
      (P.pairingIn ℤ (numbering k) α : ℝ) by norm_num,
    show algebraMap ℤ ℝ (P.pairingIn ℤ α (numbering k)) =
      (P.pairingIn ℤ α (numbering k) : ℝ) by norm_num] at hcancel
  have hrelInt :
      P.pairingIn ℤ (numbering k) α * f4RootLength i =
        P.pairingIn ℤ α (numbering k) * f4BaseRootLength k := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℝ))
    push_cast
    exact hcancel
  have hforward := f4RootCombination_pairingIn numbering hCartan hi k
  apply mul_left_cancel₀ (ne_of_gt (f4RootLength_spec i).2)
  calc
    f4RootLength i *
        (P.pairingIn ℤ α (numbering k) *
          P.pairingIn ℤ (numbering k) α) =
      P.pairingIn ℤ α (numbering k) *
        (P.pairingIn ℤ (numbering k) α * f4RootLength i) := by ring
    _ = P.pairingIn ℤ α (numbering k) *
        (P.pairingIn ℤ α (numbering k) * f4BaseRootLength k) := by
      rw [hrelInt]
    _ = f4ForwardPairing i k ^ 2 * f4BaseRootLength k := by
      rw [hforward]
      simp only [f4ForwardPairing]
      ring
    _ = f4RootLength i * f4CoxeterFingerprint i k :=
      (f4CoxeterFingerprint_spec i k).symm

private lemma f4Root_pairingData
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (B : P.InvariantForm) (base : P.Base)
    (numbering : base.support ≃ Fin 4)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
      typeF4CartanMatrix i j) (α : ι) :
    ∃ i : Fin 24, ∀ k : Fin 4,
      |P.pairingIn ℤ α (numbering.symm k)| = |f4ForwardPairing i k| ∧
      P.pairingIn ℤ α (numbering.symm k) *
          P.pairingIn ℤ (numbering.symm k) α =
        f4CoxeterFingerprint i k := by
  let simple : Fin 4 → ι := fun k => numbering.symm k
  have hCartan' : ∀ i j, P.pairingIn ℤ (simple i) (simple j) =
      typeF4CartanMatrix i j := by simpa [simple] using hCartan
  obtain ⟨i, hi | hi⟩ := isF4RootCombination_all base numbering hCartan α
  · refine ⟨i, fun k => ?_⟩
    have hf := f4RootCombination_pairingIn simple hCartan' hi k
    have hc := f4PositiveRoot_coxeterFingerprint B simple hCartan' i hi k
    exact ⟨congrArg abs hf, hc⟩
  · let := P.indexNeg
    have hneg : P.root (-α) =
        f4RootCombination P simple (typeF4PositiveCoeffs i) := by
      change P.root (P.reflectionPerm α α) = _
      rw [P.root_reflectionPerm, P.reflection_apply_self, hi]
      simp [simple]
    refine ⟨i, fun k => ?_⟩
    have hf := f4RootCombination_pairingIn simple hCartan' hneg k
    have hc := f4PositiveRoot_coxeterFingerprint B simple hCartan' i hneg k
    change P.pairingIn ℤ (P.reflectionPerm α α) (simple k) = _ at hf
    change P.pairingIn ℤ (P.reflectionPerm α α) (simple k) *
      P.pairingIn ℤ (simple k) (P.reflectionPerm α α) = _ at hc
    constructor
    · have hf' := congrArg abs hf
      simpa [simple, f4ForwardPairing] using hf'
    · simpa [simple] using hc

set_option maxHeartbeats 800000 in
private lemma f4MatrixProduct_perm_eq_id_or_reverse :
    ∀ p : Equiv.Perm (Fin 4),
      (∀ i j,
        typeF4CartanMatrix (p i) (p j) * typeF4CartanMatrix (p j) (p i) =
          typeF4CartanMatrix i j * typeF4CartanMatrix j i) →
      p = 1 ∨ p = Fin.revPerm := by
  decide

set_option maxHeartbeats 800000 in
private lemma f4RootLength_eq_one_or_two :
    ∀ i : Fin 24, f4RootLength i = 1 ∨ f4RootLength i = 2 := by
  decide

private lemma f4Root_length
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (B : P.InvariantForm) (base : P.Base)
    (numbering : base.support ≃ Fin 4)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
      typeF4CartanMatrix i j) (α : ι) :
    ∃ i : Fin 24,
      B.form (P.root α) (P.root α) =
        (f4RootLength i : ℝ) *
          B.form (P.root (numbering.symm 2)) (P.root (numbering.symm 2)) := by
  let simple : Fin 4 → ι := fun k => numbering.symm k
  have hCartan' : ∀ i j, P.pairingIn ℤ (simple i) (simple j) =
      typeF4CartanMatrix i j := by simpa [simple] using hCartan
  obtain ⟨i, hi | hi⟩ := isF4RootCombination_all base numbering hCartan α
  · exact ⟨i, f4PositiveRoot_length B simple hCartan' i hi⟩
  · let := P.indexNeg
    have hneg : P.root (-α) =
        f4RootCombination P simple (typeF4PositiveCoeffs i) := by
      change P.root (P.reflectionPerm α α) = _
      rw [P.root_reflectionPerm, P.reflection_apply_self, hi]
      simp [simple]
    have hlen := f4PositiveRoot_length B simple hCartan' i hneg
    have hrootneg : P.root (-α) = -P.root α := by
      change P.root (P.reflectionPerm α α) = -P.root α
      rw [P.root_reflectionPerm, P.reflection_apply_self]
    refine ⟨i, ?_⟩
    rw [hrootneg] at hlen
    simpa [simple] using hlen

/-- Every root of an irreducible pairing with the numbered `F₄` Cartan matrix
belongs to one of the two directed root-length classes. -/
public theorem exceptional_f4_isLongIndex_or_isShortIndex_of_cartan
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (base : P.Base) (numbering : base.support ≃ Fin 4)
    (hCartan : ∀ i j,
      P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
        typeF4CartanMatrix i j)
    (α : ι) : P.IsLongIndex α ∨ P.IsShortIndex α := by
  classical
  let _ := Fintype.ofFinite ι
  let B := (P.posRootForm ℤ).toInvariantForm
  have hratio :
      B.form (P.root (numbering.symm 0)) (P.root (numbering.symm 0)) =
        (2 : ℝ) *
          B.form (P.root (numbering.symm 2)) (P.root (numbering.symm 2)) := by
    simpa [f4BaseRootLength] using f4SimpleRoot_length B
      (fun k => (numbering.symm k : ι)) hCartan 0
  have hlength (β : ι) :
      B.form (P.root β) (P.root β) =
          B.form (P.root (numbering.symm 2)) (P.root (numbering.symm 2)) ∨
        B.form (P.root β) (P.root β) =
          B.form (P.root (numbering.symm 0)) (P.root (numbering.symm 0)) := by
    obtain ⟨i, hi⟩ := f4Root_length B base numbering hCartan β
    rcases f4RootLength_eq_one_or_two i with hi1 | hi2
    · left
      simpa [hi1] using hi
    · right
      have hi' : B.form (P.root β) (P.root β) =
          (2 : ℝ) *
            B.form (P.root (numbering.symm 2)) (P.root (numbering.symm 2)) := by
        simpa [hi2] using hi
      exact hi'.trans hratio.symm
  exact P.isLongIndex_or_isShortIndex_of_two_form_lengths B
    (numbering.symm 2) (numbering.symm 0) 2 (by norm_num) hratio hlength α

set_option maxHeartbeats 800000 in
private lemma f4SimpleTwo_not_isShort
    { ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (numbering : base.support ≃ Fin 4)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
      typeF4CartanMatrix i j) :
    ¬P.IsShortIndex (numbering.symm 2) := by
  classical
  let _ := Fintype.ofFinite ι
  rw [P.isShortIndex_iff]
  rintro ⟨β, hβ⟩
  let B := (P.posRootForm ℤ).toInvariantForm
  let t := B.form (P.root (numbering.symm 2)) (P.root (numbering.symm 2))
  have ht : t ≠ 0 := B.ne_zero (numbering.symm 2)
  obtain ⟨i, hi⟩ := f4Root_length B base numbering hCartan β
  have hsimple := f4SimpleRoot_length B
    (fun k => (numbering.symm k : ι)) hCartan 2
  have hrel := B.pairing_mul_eq_pairing_mul_swap (numbering.symm 2 : ι) β
  simp only [← P.algebraMap_pairingIn ℤ] at hrel
  rw [hi, hsimple] at hrel
  have hcancel :
      algebraMap ℤ ℝ (P.pairingIn ℤ β (numbering.symm 2)) =
        algebraMap ℤ ℝ (P.pairingIn ℤ (numbering.symm 2) β) *
          (f4RootLength i : ℝ) := by
    apply mul_right_cancel₀ ht
    simpa [f4BaseRootLength, mul_assoc, t] using hrel
  have hrelInt :
      P.pairingIn ℤ β (numbering.symm 2) =
        P.pairingIn ℤ (numbering.symm 2) β * f4RootLength i := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℝ))
    simpa using hcancel
  rcases f4RootLength_eq_one_or_two i with hlen | hlen
  · rw [hlen, mul_one] at hrelInt
    rw [hrelInt] at hβ
    omega
  · rw [hlen] at hrelInt
    rw [hrelInt] at hβ
    rw [abs_mul] at hβ
    norm_num at hβ
    have habs := abs_nonneg (P.pairingIn ℤ (numbering.symm 2) β)
    omega

private lemma f4Root_eq_of_sign_and_coxeter
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (B : P.InvariantForm) (base : P.Base)
    (numbering : base.support ≃ Fin 4)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
      typeF4CartanMatrix i j)
    {α β : ι} (hsign : base.IsPos α ↔ base.IsPos β)
    (hcox : ∀ j : Fin 4,
      P.pairingIn ℤ α (numbering.symm j) *
          P.pairingIn ℤ (numbering.symm j) α =
        P.pairingIn ℤ β (numbering.symm j) *
          P.pairingIn ℤ (numbering.symm j) β) :
    α = β := by
  have positive_eq {x y : ι} (hx : base.IsPos x) (hy : base.IsPos y)
      (hxy : ∀ j : Fin 4,
        P.pairingIn ℤ x (numbering.symm j) *
            P.pairingIn ℤ (numbering.symm j) x =
          P.pairingIn ℤ y (numbering.symm j) *
            P.pairingIn ℤ (numbering.symm j) y) :
      x = y := by
    obtain ⟨i, hi⟩ := f4Root_pairingData B base numbering hCartan x
    obtain ⟨j, hj⟩ := f4Root_pairingData B base numbering hCartan y
    have hc : ∀ k : Fin 4,
        f4CoxeterFingerprint i k = f4CoxeterFingerprint j k := by
      intro k
      exact (hi k).2.symm.trans ((hxy k).trans (hj k).2)
    apply exceptional_f4_positive_fingerprint_injective base numbering hCartan hx hy
    intro k
    rw [(hi k).1, (hj k).1]
    exact f4CoxeterFingerprint_abs_fingerprint i j hc k
  by_cases hα : base.IsPos α
  · exact positive_eq hα (hsign.mp hα) hcox
  · let := P.indexNeg
    have hβ : ¬base.IsPos β := fun h => hα (hsign.mpr h)
    have hnα : base.IsPos (-α) :=
      (RootPairing.Base.IsPos.neg_iff_not base α).mpr hα
    have hnβ : base.IsPos (-β) :=
      (RootPairing.Base.IsPos.neg_iff_not base β).mpr hβ
    apply neg_injective
    apply positive_eq hnα hnβ
    intro k
    simpa using hcox k

private theorem exceptional_f4_positiveRootDuality_unique_of_cartan
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (numbering : base.support ≃ Fin 4)
    (hCartan : ∀ i j,
      P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
        typeF4CartanMatrix i j)
    {ρ σ : Equiv.Perm ι}
    (hρ : P.IsPositiveRootDuality base ρ)
    (hσ : P.IsPositiveRootDuality base σ) :
    ρ = σ := by
  classical
  let _ := Fintype.ofFinite ι
  let B := (P.posRootForm ℤ).toInvariantForm
  have support_perm_eq_reverse
      (τ : Equiv.Perm ι) (hτ : P.IsPositiveRootDuality base τ) :
      supportPerm base numbering τ
        ((P.isPositiveRootDuality_iff base τ).mp hτ).1 = Fin.revPerm := by
    rcases (P.isPositiveRootDuality_iff base τ).mp hτ with
      ⟨hτsupport, _, hτlong, _, hτproduct⟩
    let p := supportPerm base numbering τ hτsupport
    have hp (i : Fin 4) :
        (numbering.symm (p i) : ι) = τ (numbering.symm i) := by
      exact congrArg Subtype.val
        (supportPerm_apply base numbering τ hτsupport i)
    have hproduct (i j : Fin 4) :
        typeF4CartanMatrix (p i) (p j) * typeF4CartanMatrix (p j) (p i) =
          typeF4CartanMatrix i j * typeF4CartanMatrix j i := by
      rw [← hCartan, ← hCartan, ← hCartan, ← hCartan, hp, hp]
      exact hτproduct (numbering.symm i) (numbering.symm j)
    rcases f4MatrixProduct_perm_eq_id_or_reverse p hproduct with hid | hrev
    · have hlong : P.IsLongIndex (numbering.symm 2) := by
        rw [P.isLongIndex_iff]
        refine ⟨numbering.symm 1, ?_⟩
        rw [hCartan, hCartan]
        norm_num [typeF4CartanMatrix, Fin.ext_iff]
      have hshort : P.IsShortIndex (τ (numbering.symm 2)) :=
        (hτlong (numbering.symm 2)).mp hlong
      have hp2 : (numbering.symm 2 : ι) = τ (numbering.symm 2) := by
        simpa [hid] using hp 2
      rw [← hp2] at hshort
      exact (f4SimpleTwo_not_isShort base numbering hCartan hshort).elim
    · apply exceptional_f4_matrix_duality_unique p
      exact hrev ▸ exceptional_f4_reverse_matrix_duality
  have hbase
      (τ : Equiv.Perm ι) (hτ : P.IsPositiveRootDuality base τ) (i : Fin 4) :
      τ (numbering.symm i) = numbering.symm (Fin.revPerm i) := by
    let hsupport := ((P.isPositiveRootDuality_iff base τ).mp hτ).1
    have hp := congrArg Subtype.val
      (supportPerm_apply base numbering τ hsupport i)
    rw [support_perm_eq_reverse τ hτ] at hp
    exact hp.symm
  rcases (P.isPositiveRootDuality_iff base ρ).mp hρ with
    ⟨_, hρpos, _, _, hρproduct⟩
  rcases (P.isPositiveRootDuality_iff base σ).mp hσ with
    ⟨_, hσpos, _, _, hσproduct⟩
  apply Equiv.ext
  intro α
  apply f4Root_eq_of_sign_and_coxeter B base numbering hCartan
  · exact (hρpos α).symm.trans (hσpos α)
  · intro k
    have hρk := hρproduct α (numbering.symm (Fin.revPerm k))
    have hσk := hσproduct α (numbering.symm (Fin.revPerm k))
    have hrev : Fin.revPerm (Fin.revPerm k) = k := by
      fin_cases k <;> rfl
    rw [hbase ρ hρ, hrev] at hρk
    rw [hbase σ hσ, hrev] at hσk
    exact hρk.trans hσk.symm

public theorem exceptional_f4_positiveRootDuality_unique
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (classification : RootClassification)
    (numbering : base.support ≃ Fin classification.rank)
    (hbase : ∀ i j, base.cartanMatrixIn ℤ i j =
      dynkinCartanEntry classification (numbering i) (numbering j))
    (hF4 : classification.kind = .F4 ∧ classification.rank = 4)
    {ρ σ : Equiv.Perm ι}
    (hρ : P.IsPositiveRootDuality base ρ)
    (hσ : P.IsPositiveRootDuality base σ) :
    ρ = σ := by
  rcases classification with ⟨kind, rank⟩
  rcases hF4 with ⟨rfl, rfl⟩
  apply exceptional_f4_positiveRootDuality_unique_of_cartan base numbering
  intro i j
  have h := hbase (numbering.symm i) (numbering.symm j)
  rw [RootPairing.Base.cartanMatrixIn_def (S := ℤ)] at h
  fin_cases i <;> fin_cases j <;>
    simp [dynkinCartanEntry, typeF4CartanMatrix] at h ⊢
  all_goals assumption

end Theory.AlgebraicGroup
