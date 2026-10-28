module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_6

/-!
The point group of the tensor-image model of `PSL_(m+1)` has trivial center.

For `m > 0`, an infinite algebraically closed field contains a nonzero `a` with
`a² ≠ 1`. Conjugating a transvection by the corresponding two-entry diagonal
matrix expresses every transvection as a commutator. A four-transvection
decomposition of the diagonal generators and special-linear induction then
show that `SL_(m+1)` is perfect. The case `m = 0` is handled separately: `SL_1`
is a subsingleton and hence perfect. Finally, `slTensorActionMorphism_ker`
identifies the tensor-action kernel with the source center, the first
isomorphism theorem identifies its quotient with the image closed subgroup,
and Grün's lemma makes the center of that quotient trivial.

This is the checked Fiber proof for `ag-psl-tensor-image-center-trivial`, using
the explicit tensor-image construction from `Theory.AlgebraicGroup.Instance.PSL`.
-/

set_option warningAsError false

namespace Theory.AlgebraicGroup

open scoped commutatorElement

public theorem pslClosedSubgroup_center_eq_bot
    {k : Type*} [Field k] [IsAlgClosed k] (m : ℕ) :
    letI : AlgebraicGroup
        (pslClosedSubgroupOf k (Fin (m + 1) → k)).carrierVariety :=
      (pslClosedSubgroupOf k (Fin (m + 1) → k)).carrierAlgebraicGroup
    Subgroup.center
      (Variety.Point
        (pslClosedSubgroupOf k (Fin (m + 1) → k)).carrierVariety) = ⊥ := by
  classical
  have commutator_diag2n_transvection
      {n : ℕ} {i j : Fin n} (hij : i ≠ j)
      (a : k) (ha : a ≠ 0) (b c : k)
      (hc : c = b * (a ^ 2 - 1)) :
      ⁅Matrix.SpecialLinearGroup.diag2n hij a ha,
          Matrix.SpecialLinearGroup.transvection hij b⁆ =
        (Matrix.SpecialLinearGroup.transvection hij c :
          Matrix.SpecialLinearGroup (Fin n) k) := by
    have hdiag_inv :
        (Matrix.SpecialLinearGroup.diag2n hij a ha)⁻¹ =
          Matrix.SpecialLinearGroup.diag2n hij a⁻¹ (inv_ne_zero ha) := by
      apply inv_eq_of_mul_eq_one_left
      apply Matrix.SpecialLinearGroup.ext
      intro r s
      simp only [Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.diag2n_coe,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
        Matrix.one_apply]
      by_cases hrs : r = s <;> by_cases hri : r = i <;>
        by_cases hrj : r = j <;> simp_all [ha]
    have hconj :
        Matrix.SpecialLinearGroup.diag2n hij a ha *
              Matrix.SpecialLinearGroup.transvection hij b *
            Matrix.SpecialLinearGroup.diag2n hij a⁻¹ (inv_ne_zero ha) =
          (Matrix.SpecialLinearGroup.transvection hij (a ^ 2 * b) :
            Matrix.SpecialLinearGroup (Fin n) k) := by
      apply Matrix.SpecialLinearGroup.ext
      intro r s
      simp only [Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.diag2n_coe,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.diagonal_mul,
        Matrix.mul_diagonal, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply]
      by_cases hir : i = r <;> by_cases hjs : j = s <;>
        by_cases hrs : s = r <;> simp_all [ha] <;> try field_simp <;>
          try ring_nf <;> try grind
      all_goals simp_all only [eq_comm, if_false, if_true, ite_self]
    rw [commutatorElement_def, hdiag_inv, hconj,
      Matrix.SpecialLinearGroup.transvection_inv,
      ← Matrix.SpecialLinearGroup.transvection_add]
    congr 1
    rw [hc]
    ring
  have diag2n_decompose
      {n : ℕ} {i j : Fin n} (hij : i ≠ j)
      (a : k) (ha : a ≠ 0) :
      Matrix.SpecialLinearGroup.diag2n hij a ha =
        Matrix.SpecialLinearGroup.transvection hij (a - 1) *
          Matrix.SpecialLinearGroup.transvection hij.symm 1 *
          Matrix.SpecialLinearGroup.transvection hij (a⁻¹ - 1) *
          Matrix.SpecialLinearGroup.transvection hij.symm (-a) := by
    apply Subtype.ext
    change Matrix.diagonal
        (fun r => if r = i then a else if r = j then a⁻¹ else 1) =
      (((1 + Matrix.single i j (a - 1)) *
          (1 + Matrix.single j i 1)) *
          (1 + Matrix.single i j (a⁻¹ - 1))) *
        (1 + Matrix.single j i (-a))
    have h₁ :
        (1 + Matrix.single i j (a - 1)) *
            (1 + Matrix.single j i 1) =
          1 + Matrix.single i j (a - 1) +
            Matrix.single j i 1 + Matrix.single i i (a - 1) := by
      calc
        _ = 1 + Matrix.single i j (a - 1) +
              Matrix.single j i 1 +
              Matrix.single i j (a - 1) * Matrix.single j i 1 := by
            noncomm_ring
        _ = _ := by simp
    rw [h₁]
    have h₂ :
        (1 + Matrix.single i j (a - 1) +
              Matrix.single j i 1 + Matrix.single i i (a - 1)) *
            (1 + Matrix.single i j (a⁻¹ - 1)) =
          1 + Matrix.single j i 1 + Matrix.single i i (a - 1) +
            Matrix.single j j (a⁻¹ - 1) := by
      calc
        _ = (1 + Matrix.single i j (a - 1) +
                Matrix.single j i 1 + Matrix.single i i (a - 1)) +
              (1 + Matrix.single i j (a - 1) +
                Matrix.single j i 1 + Matrix.single i i (a - 1)) *
                Matrix.single i j (a⁻¹ - 1) := by
            noncomm_ring
        _ = _ := by
          simp [add_mul, hij,
            Matrix.single_mul_single_of_ne (c := a - 1)
              i j i hij.symm (a⁻¹ - 1)]
          ext r s
          simp [Matrix.single_apply]
          split_ifs <;> simp_all <;> field_simp <;> ring
    rw [h₂]
    have h₃ :
        (1 + Matrix.single j i 1 + Matrix.single i i (a - 1) +
              Matrix.single j j (a⁻¹ - 1)) *
            (1 + Matrix.single j i (-a)) =
          1 + Matrix.single i i (a - 1) +
            Matrix.single j j (a⁻¹ - 1) := by
      calc
        _ = (1 + Matrix.single j i 1 + Matrix.single i i (a - 1) +
                Matrix.single j j (a⁻¹ - 1)) +
              (1 + Matrix.single j i 1 + Matrix.single i i (a - 1) +
                Matrix.single j j (a⁻¹ - 1)) *
                Matrix.single j i (-a) := by
            noncomm_ring
        _ = _ := by
          simp [add_mul, hij]
          ext r s
          simp [Matrix.single_apply]
          split_ifs <;> simp_all <;> field_simp <;> ring
    rw [h₃]
    ext r s
    by_cases hrs : r = s
    · subst s
      by_cases hri : r = i
      · subst r
        have hji : j ≠ i := hij.symm
        simp [Matrix.diagonal_apply, Matrix.single_apply, hij, hji, ha]
      · by_cases hrj : r = j
        · subst r
          simp [Matrix.diagonal_apply, Matrix.single_apply, hri, hij, ha]
        · have hir : i ≠ r := Ne.symm hri
          have hjr : j ≠ r := Ne.symm hrj
          simp [Matrix.diagonal_apply, Matrix.single_apply, hri, hrj,
            hir, hjr]
    · have hi : ¬ (i = r ∧ i = s) := by
        rintro ⟨rfl, rfl⟩
        exact hrs rfl
      have hj : ¬ (j = r ∧ j = s) := by
        rintro ⟨rfl, rfl⟩
        exact hrs rfl
      simp [Matrix.diagonal_apply, Matrix.single_apply, hrs, hi, hj]
  have specialLinearGroup_commutator_eq_top (hm : m ≠ 0) :
      commutator (Matrix.SpecialLinearGroup (Fin (m + 1)) k) = ⊤ := by
    letI : Nontrivial (Fin (m + 1)) :=
      Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨a, ha⟩ := Finset.exists_notMem ({0, 1, -1} : Finset k)
    have ha' : a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1 := by simpa using ha
    obtain ⟨ha0, ha1, haneg1⟩ := ha'
    have hasq : a ^ 2 ≠ 1 := sq_ne_one_iff.mpr ⟨ha1, haneg1⟩
    have htransvection
        (i j : Fin (m + 1)) (hij : i ≠ j) (c : k) :
        Matrix.SpecialLinearGroup.transvection hij c ∈
          commutator
            (Matrix.SpecialLinearGroup (Fin (m + 1)) k) := by
      have hcomm := commutator_diag2n_transvection hij a ha0
        (c / (a ^ 2 - 1)) c
        (div_mul_cancel₀ c (sub_ne_zero.mpr hasq)).symm
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator
        (Subgroup.mem_top _) (Subgroup.mem_top _)
    apply le_antisymm le_top
    intro A _
    apply Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun x ↦ x ∈ commutator
        (Matrix.SpecialLinearGroup (Fin (m + 1)) k)) A
    · intro i j hij c hc
      rw [diag2n_decompose hij c hc]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _
          (Subgroup.mul_mem _
            (htransvection i j hij (c - 1))
            (htransvection j i hij.symm 1))
          (htransvection i j hij (c⁻¹ - 1)))
        (htransvection j i hij.symm (-c))
    · exact htransvection
    · intro A B hA hB
      exact Subgroup.mul_mem _ hA hB
  have matrix_commutator_eq_top :
      commutator (Matrix.SpecialLinearGroup (Fin (m + 1)) k) = ⊤ := by
    by_cases hm : m = 0
    · subst m
      have hSL1 : Subsingleton
          (Matrix.SpecialLinearGroup (Fin (0 + 1)) k) := by
        constructor
        intro A B
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        have hi : i = 0 := Fin.eq_zero i
        have hj : j = 0 := Fin.eq_zero j
        subst i
        subst j
        have hA : A.1 0 0 = 1 := by
          simpa [Matrix.det_fin_one] using A.2
        have hB : B.1 0 0 = 1 := by
          simpa [Matrix.det_fin_one] using B.2
        exact hA.trans hB.symm
      apply le_antisymm le_top
      intro A _
      have hA : A = 1 := @Subsingleton.elim _ hSL1 A 1
      rw [hA]
      exact Subgroup.one_mem _
    · exact specialLinearGroup_commutator_eq_top hm
  have source_commutator_eq_top :
      commutator (Variety.Point (slVariety k (m + 1))) = ⊤ := by
    let e := (slPointMulEquiv (k := k) (m + 1)).symm.toMonoidHom
    have heRange : e.range =
        (⊤ : Subgroup (Variety.Point (slVariety k (m + 1)))) :=
      e.range_eq_top_of_surjective
        (slPointMulEquiv (k := k) (m + 1)).symm.surjective
    calc
      commutator (Variety.Point (slVariety k (m + 1))) =
          ⁅(⊤ : Subgroup (Variety.Point (slVariety k (m + 1)))), ⊤⁆ :=
        commutator_def _
      _ = ⁅e.range, e.range⁆ := by rw [heRange]
      _ = (commutator
          (Matrix.SpecialLinearGroup (Fin (m + 1)) k)).map e :=
        (map_commutator_eq
          (Matrix.SpecialLinearGroup (Fin (m + 1)) k) e).symm
      _ = (⊤ : Subgroup
          (Matrix.SpecialLinearGroup (Fin (m + 1)) k)).map e := by
        rw [matrix_commutator_eq_top]
      _ = e.range := by rw [MonoidHom.range_eq_map]
      _ = ⊤ := heRange
  have upperCentralSeries_eq_center {n : ℕ} (hn : n ≠ 0) :
      Subgroup.upperCentralSeries
          (Variety.Point (slVariety k (m + 1))) n =
        Subgroup.center (Variety.Point (slVariety k (m + 1))) := by
    rw [← Subgroup.upperCentralSeries_one, eq_comm]
    apply Subgroup.upperCentralSeries.eq_ge_of_eq_succ (by omega)
    apply le_antisymm
      (Subgroup.upperCentralSeries_mono
        (Variety.Point (slVariety k (m + 1))) one_le_two)
    rw [Subgroup.upperCentralSeries_one,
      ← Subgroup.commutator_top_right_eq_bot_iff_le_center,
      ← source_commutator_eq_top, Subgroup.commutator_comm,
      commutator_def]
    suffices ⁅⁅Subgroup.upperCentralSeries
          (Variety.Point (slVariety k (m + 1))) 2, ⊤⁆, ⊤⁆ = ⊥ from
      Subgroup.commutator_commutator_eq_bot_of_rotate
        (by simpa [Subgroup.commutator_comm]) this
    rw [Subgroup.commutator_top_right_eq_bot_iff_le_center,
      ← Subgroup.upperCentralSeries_one]
    exact Subgroup.commutator_upperCentralSeries_top_le
      (Variety.Point (slVariety k (m + 1))) 1
  have sourceQuotient_center_eq_bot :
      Subgroup.center
        (Variety.Point (slVariety k (m + 1)) ⧸
          Subgroup.center (Variety.Point (slVariety k (m + 1)))) = ⊥ := by
    rw [← Subgroup.upperCentralSeries_one
        (Variety.Point (slVariety k (m + 1)) ⧸
          Subgroup.center (Variety.Point (slVariety k (m + 1)))),
      ← Subgroup.comap_eq_ker_of_surjective
        (QuotientGroup.mk'_surjective _), QuotientGroup.ker_mk',
      Subgroup.comap_upperCentralSeries_quotient_center,
      upperCentralSeries_eq_center (by omega)]
  have imageCenter (n : ℕ) (hn : n = m + 1) :
      letI : AlgebraicGroup
          ((slTensorActionMorphism (k := k)
            n).imageClosedSubgroup.carrierVariety) :=
        (slTensorActionMorphism (k := k)
          n).imageClosedSubgroup.carrierAlgebraicGroup
      Subgroup.center
        (Variety.Point
          ((slTensorActionMorphism (k := k)
            n).imageClosedSubgroup.carrierVariety)) = ⊥ := by
    subst n
    letI : AlgebraicGroup
        ((slTensorActionMorphism (k := k)
          (m + 1)).imageClosedSubgroup.carrierVariety) :=
      (slTensorActionMorphism (k := k)
        (m + 1)).imageClosedSubgroup.carrierAlgebraicGroup
    let quotientEquivImage :
        (Variety.Point (slVariety k (m + 1)) ⧸
            Subgroup.center (Variety.Point (slVariety k (m + 1)))) ≃*
          Variety.Point
            ((slTensorActionMorphism (k := k)
              (m + 1)).imageClosedSubgroup.carrierVariety) :=
      (QuotientGroup.quotientMulEquivOfEq
          (slTensorActionMorphism_ker (k := k) (m + 1)).symm).trans
        ((QuotientGroup.quotientKerEquivRange
            (slTensorActionMorphism (k := k) (m + 1)).onPoints).trans
          (Equiv.mulEquiv
            (slTensorActionMorphism (k := k)
              (m + 1)).imageClosedSubgroup.pointEquiv).symm)
    refine (Subgroup.eq_bot_iff_forall _).mpr ?_
    intro x hx
    have hcenter : quotientEquivImage.symm x ∈
        Subgroup.center
          (Variety.Point (slVariety k (m + 1)) ⧸
            Subgroup.center (Variety.Point (slVariety k (m + 1)))) := by
      change quotientEquivImage.symm x ∈ Set.center _
      apply (MulEquivClass.apply_mem_center_iff quotientEquivImage).mp
      rw [quotientEquivImage.apply_symm_apply]
      change x ∈ Subgroup.center _
      exact hx
    have hone : quotientEquivImage.symm x = 1 := by
      have hbot : quotientEquivImage.symm x ∈
          (⊥ : Subgroup
            (Variety.Point (slVariety k (m + 1)) ⧸
              Subgroup.center (Variety.Point (slVariety k (m + 1))))) := by
        rw [← sourceQuotient_center_eq_bot]
        exact hcenter
      simpa using hbot
    apply quotientEquivImage.symm.injective
    simpa using hone
  exact imageCenter (Module.finrank k (Fin (m + 1) → k))
    (Module.finrank_fin_fun k)

end Theory.AlgebraicGroup
