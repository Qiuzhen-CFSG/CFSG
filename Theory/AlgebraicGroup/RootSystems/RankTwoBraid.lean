module

public import Theory.AlgebraicGroup.RootSystems.Weyl

/-! Rank-two braid words and simultaneous right descents. -/

namespace Theory.AlgebraicGroup

private lemma not_isPos_of_root_eq_add_nonneg_zsmul
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) {i j k : I} {z : ℤ}
    (hi : ¬ b.IsPos i) (hj : ¬ b.IsPos j) (hz : 0 ≤ z)
    (hroot : P.root k = P.root i + z • P.root j) :
    ¬ b.IsPos k := by
  rw [b.isPos_iff] at hi hj ⊢
  have hi' : b.height i < 0 := by
    have hne := b.height_ne_zero i
    omega
  have hj' : b.height j < 0 := by
    have hne := b.height_ne_zero j
    omega
  rw [b.height_add_zsmul hroot]
  have hnonpos : z • b.height j ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos hz hj'.le
  omega

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

private lemma reverse_alternatingWord
    {B : Type*} (i j : B) (m : ℕ) :
    (CoxeterSystem.alternatingWord i j m).reverse =
      if Even m then CoxeterSystem.alternatingWord j i m
      else CoxeterSystem.alternatingWord i j m := by
  induction m generalizing i j with
  | zero => simp [CoxeterSystem.alternatingWord]
  | succ m ih =>
      rw [CoxeterSystem.alternatingWord_succ, List.concat_eq_append,
        List.reverse_append, ih]
      simp only [List.reverse_singleton, List.singleton_append]
      by_cases hm : Even m
      · have hsucc : ¬ Even (m + 1) := by
          simpa [Nat.not_even_iff_odd] using Even.add_one hm
        rw [if_pos hm, if_neg hsucc]
        simpa [CoxeterSystem.alternatingWord_succ,
          List.concat_eq_append, hm] using
          (CoxeterSystem.alternatingWord_succ' i j m).symm
      · have hsucc : Even (m + 1) := by
          exact Odd.add_one (Nat.not_even_iff_odd.mp hm)
        rw [if_neg hm, if_pos hsucc]
        simpa [hm] using
          (CoxeterSystem.alternatingWord_succ' j i m).symm

private lemma wordLength_mul_orthogonal_pair_add_two
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (w : P.weylGroup) (i j : b.support)
    (hi : ¬ b.IsPos (P.weylGroupToPerm w i))
    (hj : ¬ b.IsPos (P.weylGroupToPerm w j))
    (hij : b.cartanMatrix i j = 0) :
    b.wordLength (w * b.wordProd [i, j]) + 2 = b.wordLength w := by
  have hji : b.cartanMatrix j i = 0 :=
    b.cartanMatrix_apply_eq_zero_iff_symm.mp hij
  have hdec0 := b.wordLength_mul_simpleReflection_of_not_isPos w i hi
  have hneg1 : ¬ b.IsPos
      (P.weylGroupToPerm (w * b.simpleReflection i) j) := by
    change ¬ b.IsPos
      (P.weylGroupToPerm w (P.reflectionPerm i j))
    apply not_isPos_of_root_eq_add_nonneg_zsmul
      (z := 0) b hj hi (by norm_num)
    rw [← P.weylGroup_apply_root, P.root_reflectionPerm,
      P.reflection_apply, smul_sub, smul_comm,
      P.root_coroot'_eq_pairing,
      pairing_eq_cast_of_cartan_eq b hji,
      P.weylGroup_apply_root, P.weylGroup_apply_root]
    module
  have hdec1 := b.wordLength_mul_simpleReflection_of_not_isPos
    (w * b.simpleReflection i) j hneg1
  simp only [b.wordProd_cons, b.wordProd_nil, mul_one] at ⊢
  have hlen : b.wordLength
      ((w * b.simpleReflection i) * b.simpleReflection j) + 2 =
        b.wordLength w := by
    omega
  simpa only [mul_assoc] using hlen

private lemma wordLength_mul_simple_braid_add_three
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (w : P.weylGroup) (i j : b.support)
    (hi : ¬ b.IsPos (P.weylGroupToPerm w i))
    (hj : ¬ b.IsPos (P.weylGroupToPerm w j))
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -1) :
    b.wordLength (w * b.wordProd [i, j, i]) + 3 = b.wordLength w := by
  have hdec0 := b.wordLength_mul_simpleReflection_of_not_isPos w i hi
  have hneg1 : ¬ b.IsPos
      (P.weylGroupToPerm (w * b.simpleReflection i) j) := by
    change ¬ b.IsPos
      (P.weylGroupToPerm w (P.reflectionPerm i j))
    apply not_isPos_of_root_eq_add_nonneg_zsmul
      (z := 1) b hj hi (by norm_num)
    rw [← P.weylGroup_apply_root, P.root_reflectionPerm,
      P.reflection_apply, smul_sub, smul_comm,
      P.root_coroot'_eq_pairing,
      pairing_eq_cast_of_cartan_eq b hji,
      P.weylGroup_apply_root, P.weylGroup_apply_root]
    module
  have hdec1 := b.wordLength_mul_simpleReflection_of_not_isPos
    (w * b.simpleReflection i) j hneg1
  have hneg2 : ¬ b.IsPos
      (P.weylGroupToPerm
        ((w * b.simpleReflection i) * b.simpleReflection j) i) := by
    change ¬ b.IsPos
      (P.weylGroupToPerm w
        (P.reflectionPerm i (P.reflectionPerm j i)))
    have hindex : P.reflectionPerm i (P.reflectionPerm j i) = j := by
      apply P.root.injective
      rw [P.root_reflectionPerm, P.root_reflectionPerm,
        P.reflection_apply, P.reflection_apply, map_sub, map_smul]
      simp only [P.root_coroot'_eq_pairing, P.pairing_same]
      rw [pairing_eq_cast_of_cartan_eq b hij,
        pairing_eq_cast_of_cartan_eq b hji]
      module
    rw [hindex]
    exact hj
  have hdec2 := b.wordLength_mul_simpleReflection_of_not_isPos
    ((w * b.simpleReflection i) * b.simpleReflection j) i hneg2
  simp only [b.wordProd_cons, b.wordProd_nil, mul_one] at ⊢
  have hlen : b.wordLength
      (((w * b.simpleReflection i) * b.simpleReflection j) *
        b.simpleReflection i) + 3 = b.wordLength w := by
    omega
  simpa only [mul_assoc] using hlen

private lemma wordLength_mul_double_braid_add_four
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (w : P.weylGroup) (i j : b.support)
    (hi : ¬ b.IsPos (P.weylGroupToPerm w i))
    (hj : ¬ b.IsPos (P.weylGroupToPerm w j))
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -2) :
    b.wordLength (w * b.wordProd [i, j, i, j]) + 4 =
      b.wordLength w := by
  have hdec0 := b.wordLength_mul_simpleReflection_of_not_isPos w i hi
  have hneg1 : ¬ b.IsPos
      (P.weylGroupToPerm (w * b.simpleReflection i) j) := by
    change ¬ b.IsPos
      (P.weylGroupToPerm w (P.reflectionPerm i j))
    apply not_isPos_of_root_eq_add_nonneg_zsmul
      (z := 2) b hj hi (by norm_num)
    rw [← P.weylGroup_apply_root, P.root_reflectionPerm,
      P.reflection_apply, smul_sub, smul_comm,
      P.root_coroot'_eq_pairing,
      pairing_eq_cast_of_cartan_eq b hji,
      P.weylGroup_apply_root, P.weylGroup_apply_root]
    module
  have hdec1 := b.wordLength_mul_simpleReflection_of_not_isPos
    (w * b.simpleReflection i) j hneg1
  have hneg2 : ¬ b.IsPos
      (P.weylGroupToPerm
        ((w * b.simpleReflection i) * b.simpleReflection j) i) := by
    change ¬ b.IsPos
      (P.weylGroupToPerm w
        (P.reflectionPerm i (P.reflectionPerm j i)))
    apply not_isPos_of_root_eq_add_nonneg_zsmul
      (z := 1) b hi hj (by norm_num)
    rw [← P.weylGroup_apply_root, P.root_reflectionPerm,
      P.root_reflectionPerm, P.reflection_apply, P.reflection_apply,
      map_sub, map_smul]
    simp only [P.root_coroot'_eq_pairing, P.pairing_same]
    rw [pairing_eq_cast_of_cartan_eq b hij,
      pairing_eq_cast_of_cartan_eq b hji]
    simp only [smul_sub, smul_comm]
    rw [P.weylGroup_apply_root, P.weylGroup_apply_root]
    module
  have hdec2 := b.wordLength_mul_simpleReflection_of_not_isPos
    ((w * b.simpleReflection i) * b.simpleReflection j) i hneg2
  have hneg3 : ¬ b.IsPos
      (P.weylGroupToPerm
        (((w * b.simpleReflection i) * b.simpleReflection j) *
          b.simpleReflection i) j) := by
    change ¬ b.IsPos
      (P.weylGroupToPerm w
        (P.reflectionPerm i
          (P.reflectionPerm j (P.reflectionPerm i j))))
    have hindex : P.reflectionPerm i
        (P.reflectionPerm j (P.reflectionPerm i j)) = j := by
      apply P.root.injective
      rw [P.root_reflectionPerm, P.root_reflectionPerm,
        P.root_reflectionPerm, P.reflection_apply, P.reflection_apply,
        P.reflection_apply, map_sub, map_sub, map_smul, map_smul]
      simp only [P.root_coroot'_eq_pairing, P.pairing_same]
      rw [pairing_eq_cast_of_cartan_eq b hij,
        pairing_eq_cast_of_cartan_eq b hji]
      simp only [map_sub, map_smul, P.root_coroot'_eq_pairing,
        P.pairing_same]
      rw [pairing_eq_cast_of_cartan_eq b hji]
      module
    rw [hindex]
    exact hj
  have hdec3 := b.wordLength_mul_simpleReflection_of_not_isPos
    (((w * b.simpleReflection i) * b.simpleReflection j) *
      b.simpleReflection i) j hneg3
  simp only [b.wordProd_cons, b.wordProd_nil, mul_one] at ⊢
  have hlen : b.wordLength
      ((((w * b.simpleReflection i) * b.simpleReflection j) *
        b.simpleReflection i) * b.simpleReflection j) + 4 =
      b.wordLength w := by
    omega
  simpa only [mul_assoc] using hlen

private lemma wordLength_mul_triple_braid_add_six
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (w : P.weylGroup) (i j : b.support)
    (hi : ¬ b.IsPos (P.weylGroupToPerm w i))
    (hj : ¬ b.IsPos (P.weylGroupToPerm w j))
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -3) :
    b.wordLength (w * b.wordProd [i, j, i, j, i, j]) + 6 =
      b.wordLength w := by
  have hdec0 := b.wordLength_mul_simpleReflection_of_not_isPos w i hi
  have hneg1 : ¬ b.IsPos
      (P.weylGroupToPerm (w * b.simpleReflection i) j) := by
    change ¬ b.IsPos
      (P.weylGroupToPerm w (P.reflectionPerm i j))
    apply not_isPos_of_root_eq_add_nonneg_zsmul
      (z := 3) b hj hi (by norm_num)
    rw [← P.weylGroup_apply_root, P.root_reflectionPerm,
      P.reflection_apply, smul_sub, smul_comm,
      P.root_coroot'_eq_pairing,
      pairing_eq_cast_of_cartan_eq b hji,
      P.weylGroup_apply_root, P.weylGroup_apply_root]
    module
  have hdec1 := b.wordLength_mul_simpleReflection_of_not_isPos
    (w * b.simpleReflection i) j hneg1
  have hneg2 : ¬ b.IsPos
      (P.weylGroupToPerm
        ((w * b.simpleReflection i) * b.simpleReflection j) i) := by
    change ¬ b.IsPos
      (P.weylGroupToPerm w
        (P.reflectionPerm i (P.reflectionPerm j i)))
    apply not_isPos_of_root_eq_add_nonneg_zsmul
      (z := 2) b hj hi (by norm_num)
    rw [← P.weylGroup_apply_root, P.root_reflectionPerm,
      P.root_reflectionPerm, P.reflection_apply, P.reflection_apply,
      map_sub, map_smul]
    simp only [P.root_coroot'_eq_pairing, P.pairing_same]
    rw [pairing_eq_cast_of_cartan_eq b hij,
      pairing_eq_cast_of_cartan_eq b hji]
    simp only [smul_sub, smul_comm]
    rw [P.weylGroup_apply_root, P.weylGroup_apply_root]
    module
  have hdec2 := b.wordLength_mul_simpleReflection_of_not_isPos
    ((w * b.simpleReflection i) * b.simpleReflection j) i hneg2
  have hneg3 : ¬ b.IsPos
      (P.weylGroupToPerm
        (((w * b.simpleReflection i) * b.simpleReflection j) *
          b.simpleReflection i) j) := by
    change ¬ b.IsPos
      (P.weylGroupToPerm w
        (P.reflectionPerm i
          (P.reflectionPerm j (P.reflectionPerm i j))))
    apply not_isPos_of_root_eq_add_nonneg_zsmul
      (z := 1) b hneg1 hj (by norm_num)
    have hlocal :
        P.root (P.reflectionPerm i
          (P.reflectionPerm j (P.reflectionPerm i j))) =
          P.root (P.reflectionPerm i j) + P.root j := by
      rw [P.root_reflectionPerm, P.root_reflectionPerm,
        P.root_reflectionPerm, P.reflection_apply, P.reflection_apply,
        P.reflection_apply, map_sub, map_sub, map_smul, map_smul]
      simp only [P.root_coroot'_eq_pairing, P.pairing_same]
      rw [pairing_eq_cast_of_cartan_eq b hij,
        pairing_eq_cast_of_cartan_eq b hji]
      simp only [map_sub, map_smul,
        P.root_coroot'_eq_pairing, P.pairing_same]
      rw [pairing_eq_cast_of_cartan_eq b hji]
      module
    rw [← P.weylGroup_apply_root w
      (P.reflectionPerm i (P.reflectionPerm j (P.reflectionPerm i j))),
      hlocal, smul_add,
      P.weylGroup_apply_root, P.weylGroup_apply_root]
    have hperm : P.weylGroupToPerm (w * b.simpleReflection i) j =
        P.weylGroupToPerm w (P.reflectionPerm i j) := by
      rfl
    rw [hperm]
    simp only [one_smul]
  have hdec3 := b.wordLength_mul_simpleReflection_of_not_isPos
    (((w * b.simpleReflection i) * b.simpleReflection j) *
      b.simpleReflection i) j hneg3
  have hneg4 : ¬ b.IsPos
      (P.weylGroupToPerm
        ((((w * b.simpleReflection i) * b.simpleReflection j) *
          b.simpleReflection i) * b.simpleReflection j) i) := by
    change ¬ b.IsPos
      (P.weylGroupToPerm w
        (P.reflectionPerm i
          (P.reflectionPerm j
            (P.reflectionPerm i (P.reflectionPerm j i)))))
    apply not_isPos_of_root_eq_add_nonneg_zsmul
      (z := 1) b hi hj (by norm_num)
    have hlocal :
        P.root (P.reflectionPerm i
          (P.reflectionPerm j
            (P.reflectionPerm i (P.reflectionPerm j i)))) =
          P.root i + P.root j := by
      rw [P.root_reflectionPerm, P.root_reflectionPerm,
        P.root_reflectionPerm, P.root_reflectionPerm,
        P.reflection_apply, P.reflection_apply, P.reflection_apply,
        P.reflection_apply, map_sub, map_sub, map_sub, map_smul,
        map_smul, map_smul]
      simp only [P.root_coroot'_eq_pairing, P.pairing_same]
      rw [pairing_eq_cast_of_cartan_eq b hij,
        pairing_eq_cast_of_cartan_eq b hji]
      simp only [map_sub, map_smul,
        P.root_coroot'_eq_pairing, P.pairing_same]
      rw [pairing_eq_cast_of_cartan_eq b hji]
      module
    rw [← P.weylGroup_apply_root w
      (P.reflectionPerm i
        (P.reflectionPerm j
          (P.reflectionPerm i (P.reflectionPerm j i)))),
      hlocal, smul_add,
      P.weylGroup_apply_root, P.weylGroup_apply_root]
    simp only [one_smul]
  have hdec4 := b.wordLength_mul_simpleReflection_of_not_isPos
    ((((w * b.simpleReflection i) * b.simpleReflection j) *
      b.simpleReflection i) * b.simpleReflection j) i hneg4
  have hneg5 : ¬ b.IsPos
      (P.weylGroupToPerm
        (((((w * b.simpleReflection i) * b.simpleReflection j) *
          b.simpleReflection i) * b.simpleReflection j) *
          b.simpleReflection i) j) := by
    change ¬ b.IsPos
      (P.weylGroupToPerm w
        (P.reflectionPerm i
          (P.reflectionPerm j
            (P.reflectionPerm i
              (P.reflectionPerm j (P.reflectionPerm i j))))))
    have hindex : P.reflectionPerm i
        (P.reflectionPerm j
          (P.reflectionPerm i
            (P.reflectionPerm j (P.reflectionPerm i j)))) = j := by
      apply P.root.injective
      rw [P.root_reflectionPerm, P.root_reflectionPerm,
        P.root_reflectionPerm, P.root_reflectionPerm,
        P.root_reflectionPerm, P.reflection_apply, P.reflection_apply,
        P.reflection_apply, P.reflection_apply, P.reflection_apply,
        map_sub, map_sub, map_sub, map_sub,
        map_smul, map_smul, map_smul, map_smul]
      simp only [P.root_coroot'_eq_pairing, P.pairing_same]
      rw [pairing_eq_cast_of_cartan_eq b hij,
        pairing_eq_cast_of_cartan_eq b hji]
      simp only [map_sub, map_smul,
        P.root_coroot'_eq_pairing, P.pairing_same]
      rw [pairing_eq_cast_of_cartan_eq b hij,
        pairing_eq_cast_of_cartan_eq b hji]
      module
    rw [hindex]
    exact hj
  have hdec5 := b.wordLength_mul_simpleReflection_of_not_isPos
    (((((w * b.simpleReflection i) * b.simpleReflection j) *
      b.simpleReflection i) * b.simpleReflection j) *
      b.simpleReflection i) j hneg5
  simp only [b.wordProd_cons, b.wordProd_nil, mul_one] at ⊢
  have hlen : b.wordLength
      ((((((w * b.simpleReflection i) * b.simpleReflection j) *
        b.simpleReflection i) * b.simpleReflection j) *
        b.simpleReflection i) * b.simpleReflection j) + 6 =
      b.wordLength w := by
    omega
  simpa only [mul_assoc] using hlen

/-- The two braid words determined by the actual pairwise reflection orders
have the same Weyl-group product. -/
public lemma _root_.RootPairing.Base.wordProd_braidWord_eq_of_orders
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (i j : b.support) :
    b.wordProd (CoxeterSystem.braidWord C i j) =
      b.wordProd (CoxeterSystem.braidWord C j i) := by
  have hlift : C.IsLiftable b.simpleReflection := by
    intro k l
    rw [hC]
    exact pow_orderOf_eq_one _
  let φ : C.Group →* P.weylGroup :=
    C.toCoxeterSystem.lift ⟨b.simpleReflection, hlift⟩
  have hsimple (k : b.support) :
      φ (C.simple k) = b.simpleReflection k :=
    C.toCoxeterSystem.lift_apply_simple hlift k
  have hword (l : List b.support) :
      φ (C.toCoxeterSystem.wordProd l) = b.wordProd l := by
    induction l with
    | nil => simp
    | cons k l ih =>
        rw [C.toCoxeterSystem.wordProd_cons, map_mul]
        change φ (C.simple k) *
          φ (C.toCoxeterSystem.wordProd l) = _
        rw [hsimple, ih, b.wordProd_cons]
  rw [← hword, C.toCoxeterSystem.wordProd_braidWord_eq, hword]

/-- A braid word determined by the actual pairwise reflection orders has
involutive Weyl-group product. -/
public lemma _root_.RootPairing.Base.wordProd_braidWord_mul_self_of_orders
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (i j : b.support) :
    b.wordProd (CoxeterSystem.braidWord C i j) *
        b.wordProd (CoxeterSystem.braidWord C i j) = 1 := by
  apply mul_eq_one_iff_eq_inv.mpr
  have hreverse (l : List b.support) :
      b.wordProd l.reverse = (b.wordProd l)⁻¹ := by
    induction l with
    | nil => simp
    | cons k l ih =>
        simp only [List.reverse_cons, b.wordProd_append,
          b.wordProd_cons, ih]
        simp
  rw [← hreverse]
  change b.wordProd (CoxeterSystem.alternatingWord i j (C i j)) =
    b.wordProd (CoxeterSystem.alternatingWord i j (C i j)).reverse
  rw [reverse_alternatingWord]
  by_cases hm : Even (C i j)
  · rw [if_pos hm]
    have hbraid := b.wordProd_braidWord_eq_of_orders C hC i j
    change b.wordProd (CoxeterSystem.alternatingWord i j (C i j)) =
      b.wordProd (CoxeterSystem.alternatingWord j i (C j i)) at hbraid
    rw [← C.symmetric i j] at hbraid
    exact hbraid
  · rw [if_neg hm]

set_option maxHeartbeats 800000 in
/-- If two simple roots are right descents of a Weyl-group element, then
right multiplication by their braid word lowers the word length by the
corresponding pairwise reflection order. -/
public theorem _root_.RootPairing.Base.wordLength_mul_braidWord_add_eq_of_two_descents
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (w : P.weylGroup) (i j : b.support)
    (hi : ¬ b.IsPos (P.weylGroupToPerm w i))
    (hj : ¬ b.IsPos (P.weylGroupToPerm w j)) :
    b.wordLength
        (w * b.wordProd (CoxeterSystem.braidWord C i j)) + C i j =
      b.wordLength w := by
  by_cases hij : i = j
  · subst j
    have hb : CoxeterSystem.braidWord C i i = [i] := by
      change CoxeterSystem.alternatingWord i i (C i i) = [i]
      rw [show C i i = 1 from C.diagonal i]
      rfl
    rw [hb, C.diagonal]
    simpa using b.wordLength_mul_simpleReflection_of_not_isPos w i hi
  have hiC := b.cartanMatrix_mem_of_ne hij
  have hjC := b.cartanMatrix_mem_of_ne (Ne.symm hij)
  have hp := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  change (b.cartanMatrix i j, b.cartanMatrix j i) ∈
    ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2),
      (-2, -1), (1, 3), (3, 1), (-1, -3), (-3, -1), (2, 2),
      (-2, -2)} : Set (ℤ × ℤ)) at hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq] at hiC hjC hp
  have hneg : P.root i ≠ -P.root j :=
    b.root_ne_neg_of_ne i.property j.property (by simpa using hij)
  have hn22 : ¬ (b.cartanMatrix i j = -2 ∧
      b.cartanMatrix j i = -2) := by
    intro h
    exact hneg ((P.pairingIn_neg_two_neg_two_iff ℤ i j).mp h)
  rcases (by aesop :
      (b.cartanMatrix i j = 0 ∧ b.cartanMatrix j i = 0) ∨
      (b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -1) ∨
      (b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -2) ∨
      (b.cartanMatrix i j = -2 ∧ b.cartanMatrix j i = -1) ∨
      (b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -3) ∨
      (b.cartanMatrix i j = -3 ∧ b.cartanMatrix j i = -1)) with
    h0 | h11 | h12 | h21 | h13 | h31
  · have horder : C i j = 2 :=
      (hC i j).trans
        (simpleReflection_mul_order_eq_two_of_cartan_zero
          b i j h0.1)
    have hb : CoxeterSystem.braidWord C i j = [i, j] := by
      change CoxeterSystem.alternatingWord i j (C i j) = [i, j]
      rw [horder]
      rfl
    rw [hb, horder]
    exact wordLength_mul_orthogonal_pair_add_two b w i j hi hj h0.1
  · have horder : C i j = 3 :=
      (hC i j).trans
        (simpleReflection_mul_order_eq_three_of_cartan_neg_one_neg_one
          b i j h11.1 h11.2)
    have hb : CoxeterSystem.braidWord C i j = [j, i, j] := by
      change CoxeterSystem.alternatingWord i j (C i j) = [j, i, j]
      rw [horder]
      rfl
    rw [hb, horder]
    exact wordLength_mul_simple_braid_add_three
      b w j i hj hi h11.2 h11.1
  · have horder : C i j = 4 :=
      (hC i j).trans
        (simpleReflection_mul_order_eq_four_of_cartan_neg_one_neg_two
          b i j h12.1 h12.2)
    have hb : CoxeterSystem.braidWord C i j = [i, j, i, j] := by
      change CoxeterSystem.alternatingWord i j (C i j) = [i, j, i, j]
      rw [horder]
      rfl
    rw [hb, horder]
    exact wordLength_mul_double_braid_add_four
      b w i j hi hj h12.1 h12.2
  · have horder : C i j = 4 :=
      (hC i j).trans
        (simpleReflection_mul_order_eq_four_of_cartan_neg_two_neg_one
          b i j h21.1 h21.2)
    have horder' : C j i = 4 := by
      rw [← C.symmetric i j]
      exact horder
    have hb : CoxeterSystem.braidWord C j i = [j, i, j, i] := by
      change CoxeterSystem.alternatingWord j i (C j i) = [j, i, j, i]
      rw [horder']
      rfl
    rw [b.wordProd_braidWord_eq_of_orders C hC i j, hb, horder]
    exact wordLength_mul_double_braid_add_four
      b w j i hj hi h21.2 h21.1
  · have horder : C i j = 6 :=
      (hC i j).trans
        (simpleReflection_mul_order_eq_six_of_cartan_neg_one_neg_three
          b i j h13.1 h13.2)
    have hb : CoxeterSystem.braidWord C i j = [i, j, i, j, i, j] := by
      change CoxeterSystem.alternatingWord i j (C i j) =
        [i, j, i, j, i, j]
      rw [horder]
      rfl
    rw [hb, horder]
    exact wordLength_mul_triple_braid_add_six
      b w i j hi hj h13.1 h13.2
  · have horder : C i j = 6 :=
      (hC i j).trans
        (simpleReflection_mul_order_eq_six_of_cartan_neg_three_neg_one
          b i j h31.1 h31.2)
    have horder' : C j i = 6 := by
      rw [← C.symmetric i j]
      exact horder
    have hb : CoxeterSystem.braidWord C j i = [j, i, j, i, j, i] := by
      change CoxeterSystem.alternatingWord j i (C j i) =
        [j, i, j, i, j, i]
      rw [horder']
      rfl
    rw [b.wordProd_braidWord_eq_of_orders C hC i j, hb, horder]
    exact wordLength_mul_triple_braid_add_six
      b w j i hj hi h31.2 h31.1

end Theory.AlgebraicGroup
