module

public import Theory.AlgebraicGroup.RootSystems.AffinePath

/-! Orders of products of two simple reflections. -/

namespace Theory.AlgebraicGroup

/-- Distinct simple roots determine distinct simple reflections. -/
public theorem _root_.RootPairing.Base.simpleReflection_injective
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) : Function.Injective b.simpleReflection := by
  intro i j hij
  have hj := (simpleReflection_unique_positiveRoot
    P b j.property (i := j)).mpr rfl
  have hperm : P.reflectionPerm i j = P.reflectionPerm j j := by
    change (RootPairing.Equiv.reflection P i).indexEquiv j =
      (RootPairing.Equiv.reflection P j).indexEquiv j
    exact congrArg (fun g : P.weylGroup => P.weylGroupToPerm g j) hij
  apply Subtype.ext
  exact ((simpleReflection_unique_positiveRoot
    P b i.property (i := j)).mp ⟨hj.1, hperm.symm ▸ hj.2⟩).symm

private lemma simpleReflection_mul_ne_one
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) {i j : b.support} (hij : i ≠ j) :
    b.simpleReflection i * b.simpleReflection j ≠ 1 := by
  intro hprod
  apply hij
  apply b.simpleReflection_injective
  have := mul_eq_one_iff_eq_inv.mp hprod
  simpa using this

private lemma pairing_eq_cast_of_cartan_eq
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic]
    (b : P.Base) {i j : b.support} {z : ℤ}
    (hij : b.cartanMatrix i j = z) :
    P.pairing i j = algebraMap ℤ R z := by
  rw [← P.algebraMap_pairingIn ℤ]
  change P.pairingIn ℤ i j = z at hij
  simpa using congrArg (algebraMap ℤ R) hij

private lemma simpleReflection_mul_sq_eq_one_of_cartan_zero
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (i j : b.support)
    (hij : b.cartanMatrix i j = 0) :
    (b.simpleReflection i * b.simpleReflection j) ^ 2 = 1 := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective P
  apply LinearEquiv.ext
  intro x
  have hijR : P.pairing i j = 0 :=
    b.cartanMatrix_apply_eq_zero_iff_pairing.mp hij
  have hji : b.cartanMatrix j i = 0 :=
    b.cartanMatrix_apply_eq_zero_iff_symm.mp hij
  have hjiR : P.pairing j i = 0 :=
    b.cartanMatrix_apply_eq_zero_iff_pairing.mp hji
  change P.reflection i (P.reflection j
    (P.reflection i (P.reflection j x))) = x
  rw [P.reflection_apply, P.reflection_apply, P.reflection_apply,
    P.reflection_apply]
  simp only [map_sub, map_smul, P.root_coroot'_eq_pairing,
    P.pairing_same]
  rw [hijR, hjiR]
  module

private lemma simpleReflection_mul_cube_eq_one_of_cartan_neg_one_neg_one
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (i j : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -1) :
    (b.simpleReflection i * b.simpleReflection j) ^ 3 = 1 := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective P
  apply LinearEquiv.ext
  intro x
  have hijR : P.pairing i j = (-1 : R) := by
    simpa using pairing_eq_cast_of_cartan_eq b hij
  have hjiR : P.pairing j i = (-1 : R) := by
    simpa using pairing_eq_cast_of_cartan_eq b hji
  change P.reflection i (P.reflection j (P.reflection i
    (P.reflection j (P.reflection i (P.reflection j x))))) = x
  rw [P.reflection_apply, P.reflection_apply, P.reflection_apply,
    P.reflection_apply, P.reflection_apply, P.reflection_apply]
  simp only [map_sub, map_smul, P.root_coroot'_eq_pairing,
    P.pairing_same]
  rw [hijR, hjiR]
  module

private lemma simpleReflection_mul_fourth_eq_one_of_cartan_neg_one_neg_two
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (i j : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -2) :
    (b.simpleReflection i * b.simpleReflection j) ^ 4 = 1 := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective P
  apply LinearEquiv.ext
  intro x
  have hijR : P.pairing i j = (-1 : R) := by
    simpa using pairing_eq_cast_of_cartan_eq b hij
  have hjiR : P.pairing j i = (-2 : R) := by
    simpa using pairing_eq_cast_of_cartan_eq b hji
  change P.reflection i (P.reflection j (P.reflection i
    (P.reflection j (P.reflection i (P.reflection j
      (P.reflection i (P.reflection j x))))))) = x
  rw [P.reflection_apply, P.reflection_apply, P.reflection_apply,
    P.reflection_apply, P.reflection_apply, P.reflection_apply,
    P.reflection_apply, P.reflection_apply]
  simp only [map_sub, map_smul, P.root_coroot'_eq_pairing,
    P.pairing_same]
  rw [hijR, hjiR]
  module

private lemma simpleReflection_mul_sixth_eq_one_of_cartan_neg_one_neg_three
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (i j : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -3) :
    (b.simpleReflection i * b.simpleReflection j) ^ 6 = 1 := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective P
  apply LinearEquiv.ext
  intro x
  have hijR : P.pairing i j = (-1 : R) := by
    simpa using pairing_eq_cast_of_cartan_eq b hij
  have hjiR : P.pairing j i = (-3 : R) := by
    simpa using pairing_eq_cast_of_cartan_eq b hji
  change P.reflection i (P.reflection j (P.reflection i
    (P.reflection j (P.reflection i (P.reflection j
      (P.reflection i (P.reflection j (P.reflection i
        (P.reflection j (P.reflection i (P.reflection j x))))))))))) = x
  rw [P.reflection_apply, P.reflection_apply, P.reflection_apply,
    P.reflection_apply, P.reflection_apply, P.reflection_apply,
    P.reflection_apply, P.reflection_apply, P.reflection_apply,
    P.reflection_apply, P.reflection_apply, P.reflection_apply]
  simp only [map_sub, map_smul, P.root_coroot'_eq_pairing,
    P.pairing_same]
  rw [hijR, hjiR]
  module

/-- Orthogonal simple roots have a product of reflections of order two. -/
public theorem simpleReflection_mul_order_eq_two_of_cartan_zero
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (i j : b.support)
    (hij : b.cartanMatrix i j = 0) :
    orderOf (b.simpleReflection i * b.simpleReflection j) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
    (simpleReflection_mul_sq_eq_one_of_cartan_zero b i j hij)
  apply simpleReflection_mul_ne_one b
  intro heq
  subst j
  rw [b.cartanMatrix_apply_same] at hij
  norm_num at hij

/-- A simple bond gives a product of simple reflections of order three. -/
public theorem simpleReflection_mul_order_eq_three_of_cartan_neg_one_neg_one
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (i j : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -1) :
    orderOf (b.simpleReflection i * b.simpleReflection j) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
    (simpleReflection_mul_cube_eq_one_of_cartan_neg_one_neg_one
      b i j hij hji)
  apply simpleReflection_mul_ne_one b
  intro heq
  subst j
  rw [b.cartanMatrix_apply_same] at hij
  norm_num at hij

/-- A Cartan pair `(-1, -2)` gives a product of simple reflections of order
four. -/
public theorem simpleReflection_mul_order_eq_four_of_cartan_neg_one_neg_two
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (i j : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -2) :
    orderOf (b.simpleReflection i * b.simpleReflection j) = 4 := by
  have hpow :=
    simpleReflection_mul_fourth_eq_one_of_cartan_neg_one_neg_two
      b i j hij hji
  apply orderOf_eq_of_pow_and_pow_div_prime (n := 4) (by norm_num) hpow
  intro p hp hpd
  have hp2 : p = 2 := by
    have hple : p ≤ 4 := Nat.le_of_dvd (by norm_num) hpd
    have hpge : 2 ≤ p := hp.two_le
    interval_cases p
    · rfl
    · norm_num at hpd
    · have hnot : ¬ Nat.Prime 4 := by
        rw [Nat.prime_def_lt']
        intro h
        exact h.2 2 (by norm_num) (by norm_num) (by norm_num)
      exact (hnot hp).elim
  subst p
  norm_num
  intro hsq
  have hroot := congrArg
    (fun g : P.weylGroup => g • P.root i) hsq
  have hijR : P.pairing i j = (-1 : R) := by
    simpa using pairing_eq_cast_of_cartan_eq b hij
  have hjiR : P.pairing j i = (-2 : R) := by
    simpa using pairing_eq_cast_of_cartan_eq b hji
  change P.reflection i (P.reflection j
    (P.reflection i (P.reflection j (P.root i)))) = P.root i at hroot
  rw [P.reflection_apply, P.reflection_apply, P.reflection_apply,
    P.reflection_apply] at hroot
  simp only [map_sub, map_smul, P.root_coroot'_eq_pairing,
    P.pairing_same] at hroot
  rw [hijR, hjiR] at hroot
  norm_num at hroot
  exact P.ne_zero i hroot

/-- A Cartan pair `(-2, -1)` gives a product of simple reflections of order
four. -/
public theorem simpleReflection_mul_order_eq_four_of_cartan_neg_two_neg_one
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (i j : b.support)
    (hij : b.cartanMatrix i j = -2)
    (hji : b.cartanMatrix j i = -1) :
    orderOf (b.simpleReflection i * b.simpleReflection j) = 4 := by
  calc
    orderOf (b.simpleReflection i * b.simpleReflection j) =
        orderOf (b.simpleReflection j * b.simpleReflection i) := by
      rw [← orderOf_inv]
      simp only [mul_inv_rev, b.simpleReflection_inv]
    _ = 4 :=
      simpleReflection_mul_order_eq_four_of_cartan_neg_one_neg_two
        b j i hji hij

/-- A Cartan pair `(-1, -3)` gives a product of simple reflections of order
six. -/
public theorem simpleReflection_mul_order_eq_six_of_cartan_neg_one_neg_three
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (i j : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -3) :
    orderOf (b.simpleReflection i * b.simpleReflection j) = 6 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (n := 6) (by norm_num)
    (simpleReflection_mul_sixth_eq_one_of_cartan_neg_one_neg_three
      b i j hij hji)
  intro p hp hpd
  have hple : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpd
  have hpge : 2 ≤ p := hp.two_le
  interval_cases p
  · norm_num
    intro hcube
    have hroot := congrArg
      (fun g : P.weylGroup => g • P.root i) hcube
    have hijR : P.pairing i j = (-1 : R) := by
      simpa using pairing_eq_cast_of_cartan_eq b hij
    have hjiR : P.pairing j i = (-3 : R) := by
      simpa using pairing_eq_cast_of_cartan_eq b hji
    change P.reflection i (P.reflection j (P.reflection i
      (P.reflection j (P.reflection i (P.reflection j (P.root i)))))) =
        P.root i at hroot
    rw [P.reflection_apply, P.reflection_apply, P.reflection_apply,
      P.reflection_apply, P.reflection_apply, P.reflection_apply] at hroot
    simp only [map_sub, map_smul, P.root_coroot'_eq_pairing,
      P.pairing_same] at hroot
    rw [hijR, hjiR] at hroot
    norm_num at hroot
    exact P.ne_zero i hroot
  · norm_num
    intro hsq
    have hroot := congrArg
      (fun g : P.weylGroup => g • P.root i) hsq
    have hijR : P.pairing i j = (-1 : R) := by
      simpa using pairing_eq_cast_of_cartan_eq b hij
    have hjiR : P.pairing j i = (-3 : R) := by
      simpa using pairing_eq_cast_of_cartan_eq b hji
    change P.reflection i (P.reflection j
      (P.reflection i (P.reflection j (P.root i)))) = P.root i at hroot
    rw [P.reflection_apply, P.reflection_apply, P.reflection_apply,
      P.reflection_apply] at hroot
    simp only [map_sub, map_smul, P.root_coroot'_eq_pairing,
      P.pairing_same] at hroot
    rw [hijR, hjiR] at hroot
    norm_num at hroot
    exact P.ne_zero j hroot
  · have hnot : ¬ Nat.Prime 4 := by
      rw [Nat.prime_def_lt']
      intro h
      exact h.2 2 (by norm_num) (by norm_num) (by norm_num)
    exact (hnot hp).elim
  · norm_num at hpd
  · have hnot : ¬ Nat.Prime 6 := by
      rw [Nat.prime_def_lt']
      intro h
      exact h.2 2 (by norm_num) (by norm_num) (by norm_num)
    exact (hnot hp).elim

/-- A Cartan pair `(-3, -1)` gives a product of simple reflections of order
six. -/
public theorem simpleReflection_mul_order_eq_six_of_cartan_neg_three_neg_one
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (i j : b.support)
    (hij : b.cartanMatrix i j = -3)
    (hji : b.cartanMatrix j i = -1) :
    orderOf (b.simpleReflection i * b.simpleReflection j) = 6 := by
  calc
    orderOf (b.simpleReflection i * b.simpleReflection j) =
        orderOf (b.simpleReflection j * b.simpleReflection i) := by
      rw [← orderOf_inv]
      simp only [mul_inv_rev, b.simpleReflection_inv]
    _ = 6 :=
      simpleReflection_mul_order_eq_six_of_cartan_neg_one_neg_three
        b j i hji hij

end Theory.AlgebraicGroup
