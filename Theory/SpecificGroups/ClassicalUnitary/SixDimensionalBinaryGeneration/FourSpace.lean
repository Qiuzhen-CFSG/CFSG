module

public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinaryGeneration.Reduction

/-!
# Transvection generation of the embedded four-dimensional unitary block

We prove that every special unitary matrix fixing coordinates 0 and 1 belongs
to the inverse image of the specified projective transvection subgroup.
Column reduction first fixes coordinate 2. For the remaining three-space,
two-coordinate transvections give swaps and determinant-one pair scalings.
An explicit four-transvection word fixes coordinate 2 and sends the vector
with coordinates (1, 1, 1) on 3, 4, 5 to the third coordinate vector.
Pair scalings normalize any three nonzero entries, using coordinate 2 to
balance determinants; a final pair scaling restores that coordinate.
The two-space reduces by swaps and scalings, and determinant one fixes the
last coordinate.

This supplies the embedded-block premise of the projective U₆(2) generation
argument used for GLS3 Table 5.3t (`refs/KGroup/GLS3/Chapter5(sec3-).tex`).
The calculation uses the literal GF(4) matrix model and actual isotropic
transvections, without simplicity or Fischer recognition assumptions.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
namespace Theory.SpecificGroups.U6Two.Generation

private theorem pairing_smul_left (c : Field) (x y : Vector) :
    pairing (c • x) y = conjugation c * pairing x y := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, map_mul]
  unfold dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_assoc _ _ _

private theorem pairDirection_norm (i j : Fin 6) (hij : i ≠ j)
    (c : Field) (hc : c ≠ 0) :
    hermitianNorm (basisVector i + c • basisVector j) = 0 := by
  apply sum_isotropic_of_orthogonal_unit (basisVector_norm i)
  · rw [hermitianNorm_smul, conjugation_mul_self_of_ne_zero c hc,
      basisVector_norm, one_mul]
  · rw [pairing_basis_left]
    simp [basisVector, hij]

/-- The direction eᵢ + c eⱼ gives a swap with reciprocal scalar factors. -/
private noncomputable def pairSwap (i j : Fin 6) (hij : i ≠ j)
    (c : Field) (hc : c ≠ 0) : form.specialSubgroup :=
  unitaryTransvection _ (pairDirection_norm i j hij c hc)

private theorem pairSwap_apply (i j : Fin 6) (hij : i ≠ j)
    (c : Field) (hc : c ≠ 0) (x : Vector) (k : Fin 6) :
    ((pairSwap i j hij c hc).val • x) k =
      if k = i then conjugation c * x j else if k = j then c * x i else x k := by
  rw [pairSwap, unitaryTransvection_smul]
  change x k + pairing (basisVector i + c • basisVector j) x *
    (basisVector i + c • basisVector j) k = _
  rw [pairing_add_left, pairing_basis_left, pairing_smul_left, pairing_basis_left]
  by_cases hki : k = i
  · subst k
    simp [basisVector, hij, CharTwo.add_self_eq_zero, ← add_assoc]
  · by_cases hkj : k = j
    · subst k
      simp only [basisVector, Pi.add_apply, Pi.single_eq_of_ne hki, Pi.single_eq_same,
        Pi.smul_apply, smul_eq_mul, mul_one, zero_add, if_neg hki]
      rw [add_mul, mul_assoc, mul_comm (x j) c, ← mul_assoc,
        conjugation_mul_self_of_ne_zero c hc, one_mul]
      simp only [ite_true]
      rw [mul_comm (x i) c, add_comm (c * x i), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    · simp [basisVector, hki, hkj]

/-- Two supported swaps scale the pair by c and its conjugate. -/
private noncomputable def pairScale (i j : Fin 6) (hij : i ≠ j)
    (c : Field) (hc : c ≠ 0) : form.specialSubgroup :=
  pairSwap i j hij 1 one_ne_zero * pairSwap i j hij c hc

private theorem pairScale_mem (i j : Fin 6) (hij : i ≠ j)
    (c : Field) (hc : c ≠ 0) : pairScale i j hij c hc ∈ generatedSpecial :=
  generatedSpecial.mul_mem (unitaryTransvection_mem _ _) (unitaryTransvection_mem _ _)

private theorem pairScale_apply (i j : Fin 6) (hij : i ≠ j)
    (c : Field) (hc : c ≠ 0) (x : Vector) (k : Fin 6) :
    ((pairScale i j hij c hc).val • x) k =
      if k = i then c * x k else if k = j then conjugation c * x k else x k := by
  simp only [pairScale, Subgroup.coe_mul, mul_smul, pairSwap_apply, map_one, one_mul]
  by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all [Ne.symm hij]

private theorem pairScale_basis (i j : Fin 6) (hij : i ≠ j)
    (c : Field) (hc : c ≠ 0) (k : Fin 6) :
    (pairScale i j hij c hc).val • basisVector k =
      (if k = i then c else if k = j then conjugation c else 1) • basisVector k := by
  ext l
  rw [pairScale_apply]
  by_cases hl : l = k <;> simp [basisVector, hl]

private theorem exists_primitive_scalar :
    ∃ w : Field, w ≠ 0 ∧ w ≠ 1 ∧ 1 + w + w ^ 2 = 0 := by
  classical
  let := Fintype.ofFinite Field
  obtain ⟨w, hw0, hw1⟩ : ∃ w : Field, w ≠ 0 ∧ w ≠ 1 := by
    by_contra h
    push Not at h
    have hs : (Finset.univ : Finset Field) ⊆ {0, 1} := by
      intro c _
      by_cases hc : c = 0
      · simp [hc]
      · simp [h c hc]
    have hc := Finset.card_le_card hs
    have hcard : Fintype.card Field = 4 := by
      simpa only [Nat.card_eq_fintype_card] using field_card
    simp [hcard] at hc
  refine ⟨w, hw0, hw1, ?_⟩
  have hp : w ^ 3 = 1 := by
    simpa only [conjugation_apply, ← pow_succ] using conjugation_mul_self_of_ne_zero w hw0
  have hz : (w - 1) * (1 + w + w ^ 2) = 0 := by
    calc
      _ = w ^ 3 - 1 := by ring
      _ = 0 := by rw [hp, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hw1)

set_option linter.unusedSimpArgs false in
/-- Only these two actions of the Fourier word are needed for column reduction.
The intermediate vector equalities keep the checked calculation small. -/
private theorem exists_fourier :
    ∃ H : form.specialSubgroup, H ∈ generatedSpecial ∧
      (∀ i : Fin 6, i.val < 3 → H.val • basisVector i = basisVector i) ∧
      H.val • ![0, 0, 0, 1, 1, 1] = basisVector 3 := by
  obtain ⟨w, hw0, hw1, hw⟩ := exists_primitive_scalar
  have hw3 : w ^ 3 = 1 := by
    simpa only [conjugation_apply, ← pow_succ] using conjugation_mul_self_of_ne_zero w hw0
  let v1 : Vector := ![0, 0, 1, 1, 0, 0]
  let v2 : Vector := ![0, 0, 1, 1, w, w]
  let v3 : Vector := ![0, 0, 1, w ^ 2, 1, 1]
  let v4 : Vector := ![0, 0, 1, w ^ 2, w ^ 2, w ^ 2]
  have hn (x : Field) (hx : x ≠ 0) : conjugation x * x = 1 :=
    conjugation_mul_self_of_ne_zero x hx
  have hv1 : hermitianNorm v1 = 0 := by
    simp [v1, hermitianNorm, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  have hv2 : hermitianNorm v2 = 0 := by
    simp [v2, hermitianNorm, dotProduct, Fin.sum_univ_succ, hn w hw0,
      CharTwo.add_self_eq_zero]
  have hv3 : hermitianNorm v3 = 0 := by
    simp [v3, hermitianNorm, dotProduct, Fin.sum_univ_succ, ← mul_pow, hn w hw0,
      CharTwo.add_self_eq_zero]
  have hv4 : hermitianNorm v4 = 0 := by
    simp [v4, hermitianNorm, dotProduct, Fin.sum_univ_succ, ← mul_pow, hn w hw0,
      CharTwo.add_self_eq_zero]
  let H := unitaryTransvection v1 hv1 * unitaryTransvection v2 hv2 *
    unitaryTransvection v3 hv3 * unitaryTransvection v4 hv4
  -- Rightmost factors act first. First check that coordinate 2 is restored.
  have ha4 : (unitaryTransvection v4 hv4).val • basisVector 2 = ![0, 0, 0, w ^ 2, w ^ 2, w ^ 2] := by
    ext k
    fin_cases k <;> simp [unitaryTransvection_smul, v4, basisVector,
      dotProduct, Fin.sum_univ_succ, conjugation_apply, vecHead, vecTail]
    all_goals try ring_nf
    all_goals simp [CharTwo.ofNat_eq_mod (R := Field), hw]
  have ha3 : (unitaryTransvection v3 hv3).val • ![0, 0, 0, w ^ 2, w ^ 2, w ^ 2] = ![0, 0, 1, 0, w, w] := by
    ext k
    fin_cases k <;> simp [unitaryTransvection_smul, v3, basisVector,
      dotProduct, Fin.sum_univ_succ, conjugation_apply, vecHead, vecTail]
    all_goals try ring_nf
    all_goals norm_num [CharTwo.ofNat_eq_mod (R := Field), CharTwo.add_self_eq_zero,
      pow_eq_pow_mod 3 hw3, pow_eq_pow_mod 4 hw3, pow_eq_pow_mod 5 hw3, pow_eq_pow_mod 6 hw3, pow_eq_pow_mod 7 hw3, pow_eq_pow_mod 8 hw3]
    all_goals try ring_nf
    all_goals simp [CharTwo.ofNat_eq_mod (R := Field), hw]
    all_goals linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := Field)])) hw
  have ha2 : (unitaryTransvection v2 hv2).val • ![0, 0, 1, 0, w, w] = ![0, 0, 0, 1, 0, 0] := by
    ext k
    fin_cases k <;> simp [unitaryTransvection_smul, v2, basisVector,
      dotProduct, Fin.sum_univ_succ, conjugation_apply, vecHead, vecTail]
    all_goals try ring_nf
    all_goals norm_num [CharTwo.ofNat_eq_mod (R := Field), CharTwo.add_self_eq_zero,
      pow_eq_pow_mod 3 hw3, pow_eq_pow_mod 4 hw3, pow_eq_pow_mod 5 hw3, pow_eq_pow_mod 6 hw3, pow_eq_pow_mod 7 hw3, pow_eq_pow_mod 8 hw3]
    all_goals simp [CharTwo.ofNat_eq_mod (R := Field), hw]
  have ha1 : (unitaryTransvection v1 hv1).val • ![0, 0, 0, 1, 0, 0] = basisVector 2 := by
    ext k
    fin_cases k <;> simp [unitaryTransvection_smul, v1, basisVector,
      dotProduct, Fin.sum_univ_succ, conjugation_apply, vecHead, vecTail]
    all_goals try ring_nf
    all_goals simp [CharTwo.ofNat_eq_mod (R := Field), hw]
  -- The same word sends the all-one three-tail to e₃.
  have hb4 : (unitaryTransvection v4 hv4).val • ![0, 0, 0, 1, 1, 1] = ![0, 0, w, 0, 0, 0] := by
    ext k
    fin_cases k <;> simp [unitaryTransvection_smul, v4, basisVector,
      dotProduct, Fin.sum_univ_succ, conjugation_apply, vecHead, vecTail]
    all_goals try ring_nf
    all_goals norm_num [CharTwo.ofNat_eq_mod (R := Field), CharTwo.add_self_eq_zero,
      pow_eq_pow_mod 3 hw3, pow_eq_pow_mod 4 hw3, pow_eq_pow_mod 5 hw3, pow_eq_pow_mod 6 hw3, pow_eq_pow_mod 7 hw3, pow_eq_pow_mod 8 hw3]
    all_goals try ring_nf
    all_goals simp [CharTwo.ofNat_eq_mod (R := Field), hw]
  have hb3 : (unitaryTransvection v3 hv3).val • ![0, 0, w, 0, 0, 0] = ![0, 0, 0, 1, w, w] := by
    ext k
    fin_cases k <;> simp [unitaryTransvection_smul, v3, basisVector,
      dotProduct, Fin.sum_univ_succ, conjugation_apply, vecHead, vecTail]
    all_goals try ring_nf
    all_goals norm_num [CharTwo.ofNat_eq_mod (R := Field), CharTwo.add_self_eq_zero,
      pow_eq_pow_mod 3 hw3, pow_eq_pow_mod 4 hw3, pow_eq_pow_mod 5 hw3, pow_eq_pow_mod 6 hw3, pow_eq_pow_mod 7 hw3, pow_eq_pow_mod 8 hw3]
    all_goals try ring_nf
    all_goals simp [CharTwo.ofNat_eq_mod (R := Field), hw]
  have hb2 : (unitaryTransvection v2 hv2).val • ![0, 0, 0, 1, w, w] = ![0, 0, 1, 0, 0, 0] := by
    ext k
    fin_cases k <;> simp [unitaryTransvection_smul, v2, basisVector,
      dotProduct, Fin.sum_univ_succ, conjugation_apply, vecHead, vecTail]
    all_goals try ring_nf
    all_goals norm_num [CharTwo.ofNat_eq_mod (R := Field), CharTwo.add_self_eq_zero,
      pow_eq_pow_mod 3 hw3, pow_eq_pow_mod 4 hw3, pow_eq_pow_mod 5 hw3, pow_eq_pow_mod 6 hw3, pow_eq_pow_mod 7 hw3, pow_eq_pow_mod 8 hw3]
    all_goals simp [CharTwo.ofNat_eq_mod (R := Field), hw]
  have hb1 : (unitaryTransvection v1 hv1).val • ![0, 0, 1, 0, 0, 0] = basisVector 3 := by
    ext k
    fin_cases k <;> simp [unitaryTransvection_smul, v1, basisVector,
      dotProduct, Fin.sum_univ_succ, conjugation_apply, vecHead, vecTail]
    all_goals try ring_nf
    all_goals simp [CharTwo.ofNat_eq_mod (R := Field), hw]
  refine ⟨H, ?_, ?_, ?_⟩
  · exact generatedSpecial.mul_mem (generatedSpecial.mul_mem
      (generatedSpecial.mul_mem (unitaryTransvection_mem _ _) (unitaryTransvection_mem _ _))
      (unitaryTransvection_mem _ _)) (unitaryTransvection_mem _ _)
  · intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi' with rfl | rfl | rfl
    · simp only [H, Subgroup.coe_mul, mul_smul]
      rw [transvection_fixes_basis hv4 0 (by simp [v4]),
        transvection_fixes_basis hv3 0 (by simp [v3]),
        transvection_fixes_basis hv2 0 (by simp [v2]),
        transvection_fixes_basis hv1 0 (by simp [v1])]
    · simp only [H, Subgroup.coe_mul, mul_smul]
      rw [transvection_fixes_basis hv4 1 (by simp [v4]),
        transvection_fixes_basis hv3 1 (by simp [v3]),
        transvection_fixes_basis hv2 1 (by simp [v2]),
        transvection_fixes_basis hv1 1 (by simp [v1])]
    · simp only [H, Subgroup.coe_mul, mul_smul, ha4, ha3, ha2, ha1]
  · simp only [H, Subgroup.coe_mul, mul_smul, hb4, hb3, hb2, hb1]

private theorem action_smul (A : form.specialSubgroup) (c : Field) (x : Vector) :
    A.val • (c • x) = c • (A.val • x) := mulVec_smul _ _ _

private theorem dense_reduction (x : Vector)
    (hxprev : ∀ j : Fin 6, j.val < 3 → x j = 0)
    (hx3 : x 3 ≠ 0) (hx4 : x 4 ≠ 0) (hx5 : x 5 ≠ 0) :
    ∃ A : form.specialSubgroup, A ∈ generatedSpecial ∧
      (∀ j : Fin 6, j.val < 3 → A.val • basisVector j = basisVector j) ∧
      A.val • x = basisVector 3 := by
  obtain ⟨H, hH, hHfix, hHmove⟩ := exists_fourier
  -- Normalize the three entries, balancing each scaling on coordinate 2.
  let D3 := pairScale 3 2 (by decide) (conjugation (x 3)) (by simpa using hx3)
  let D4 := pairScale 4 2 (by decide) (conjugation (x 4)) (by simpa using hx4)
  let D5 := pairScale 5 2 (by decide) (conjugation (x 5)) (by simpa using hx5)
  let D := D5 * D4 * D3
  let p := x 3 * (x 4 * x 5)
  have hp : p ≠ 0 := mul_ne_zero hx3 (mul_ne_zero hx4 hx5)
  -- After applying H, coordinate 4 is spare and restores coordinate 2.
  let E := pairScale 2 4 (by decide) (conjugation p) (by simpa using hp)
  have hDmem : D ∈ generatedSpecial := generatedSpecial.mul_mem
    (generatedSpecial.mul_mem (pairScale_mem _ _ _ _ _) (pairScale_mem _ _ _ _ _))
    (pairScale_mem _ _ _ _ _)
  have hDfix (j : Fin 6) (hj : j.val < 2) : D.val • basisVector j = basisVector j := by
    have hj2 : j ≠ 2 := by omega
    have hj3 : j ≠ 3 := by omega
    have hj4 : j ≠ 4 := by omega
    have hj5 : j ≠ 5 := by omega
    simp [D, D3, D4, D5, Subgroup.coe_mul, mul_smul, pairScale_basis, hj2, hj3, hj4, hj5]
  have hD2 : D.val • basisVector 2 = p • basisVector 2 := by
    simp only [D, D3, D4, D5, Subgroup.coe_mul, mul_smul]
    simp only [pairScale_basis, action_smul]
    rw [conjugation_involutive, conjugation_involutive, conjugation_involutive]
    simp [smul_smul, p]
  have hDx : D.val • x = ![0, 0, 0, 1, 1, 1] := by
    have hx0 := hxprev 0 (by decide)
    have hx1 := hxprev 1 (by decide)
    have hx2 := hxprev 2 (by decide)
    ext k
    fin_cases k <;>
      simp [D, D3, D4, D5, Subgroup.coe_mul, mul_smul, pairScale_apply,
        hx0, hx1, hx2,
        conjugation_mul_self_of_ne_zero _ hx3, conjugation_mul_self_of_ne_zero _ hx4,
        conjugation_mul_self_of_ne_zero _ hx5]
  refine ⟨E * H * D, generatedSpecial.mul_mem
    (generatedSpecial.mul_mem (pairScale_mem _ _ _ _ _) hH) hDmem, ?_, ?_⟩
  · intro j hj
    by_cases hj2 : j = 2
    · subst j
      simp only [Subgroup.coe_mul, mul_smul, hD2, action_smul, hHfix 2 (by decide)]
      rw [show E.val • basisVector 2 = conjugation p • basisVector 2 from by
        simp [E, pairScale_basis]]
      rw [smul_smul, mul_comm p, conjugation_mul_self_of_ne_zero _ hp, one_smul]
    · have hjlt : j.val < 2 := by omega
      rw [Subgroup.coe_mul, mul_smul, Subgroup.coe_mul, mul_smul, hDfix j hjlt, hHfix j hj]
      have hj4 : j ≠ 4 := by omega
      simp [E, pairScale_basis, hj2, hj4]
  · rw [Subgroup.coe_mul, mul_smul, Subgroup.coe_mul, mul_smul, hDx, hHmove]
    simp [E, pairScale_basis]

private theorem three_tail_reduction (x : Vector) (hx : hermitianNorm x = 1)
    (hxprev : ∀ j : Fin 6, j.val < 3 → x j = 0) :
    ∃ A : form.specialSubgroup, A ∈ generatedSpecial ∧
      (∀ j : Fin 6, j.val < 3 → A.val • basisVector j = basisVector j) ∧
      A.val • x = basisVector 3 := by
  by_cases hz : ∃ j : Fin 6, 3 < j.val ∧ x j = 0
  · obtain ⟨j, hj, hxj⟩ := hz
    apply reduction_of_perpendicular 3 x (basisVector j) hx (basisVector_norm j)
    · rw [pairing_basis_right, hxj, map_zero]
    · have h3j : (3 : Fin 6) ≠ j := by omega
      simp [basisVector, h3j]
    · exact hxprev
    · intro k hk
      have hkj : k ≠ j := by omega
      simp [basisVector, hkj]
  · have hx4 : x 4 ≠ 0 := fun h => hz ⟨4, by decide, h⟩
    have hx5 : x 5 ≠ 0 := fun h => hz ⟨5, by decide, h⟩
    have hx3 : x 3 ≠ 0 := by
      intro h
      have hx0 := hxprev 0 (by decide)
      have hx1 := hxprev 1 (by decide)
      have hx2 := hxprev 2 (by decide)
      simp [hermitianNorm, dotProduct, Fin.sum_univ_succ, hx0, hx1, hx2, h,
        conjugation_mul_self_of_ne_zero _ hx4, conjugation_mul_self_of_ne_zero _ hx5,
        CharTwo.add_self_eq_zero] at hx
    exact dense_reduction x hxprev hx3 hx4 hx5

private theorem two_tail_reduction (x : Vector) (hx : hermitianNorm x = 1)
    (hxprev : ∀ j : Fin 6, j.val < 4 → x j = 0) :
    ∃ A : form.specialSubgroup, A ∈ generatedSpecial ∧
      (∀ j : Fin 6, j.val < 4 → A.val • basisVector j = basisVector j) ∧
      A.val • x = basisVector 4 := by
  have hx0 := hxprev 0 (by decide)
  have hx1 := hxprev 1 (by decide)
  have hx2 := hxprev 2 (by decide)
  have hx3 := hxprev 3 (by decide)
  have hn : conjugation (x 4) * x 4 + conjugation (x 5) * x 5 = 1 := by
    simpa [hermitianNorm, dotProduct, Fin.sum_univ_succ, hx0, hx1, hx2, hx3] using hx
  by_cases hx5 : x 5 = 0
  · have hx4 : x 4 ≠ 0 := by intro h; simp [h, hx5] at hn
    let A := pairScale 4 5 (by decide) (conjugation (x 4)) (by simpa using hx4)
    refine ⟨A, pairScale_mem _ _ _ _ _, ?_, ?_⟩
    · intro j hj
      have hj4 : j ≠ 4 := by omega
      have hj5 : j ≠ 5 := by omega
      simp [A, pairScale_basis, hj4, hj5]
    · ext k
      fin_cases k <;> simp [A, pairScale_apply, basisVector, hx0, hx1, hx2, hx3, hx5,
        conjugation_mul_self_of_ne_zero _ hx4]
  · have hx4 : x 4 = 0 := by
      by_contra h
      rw [conjugation_mul_self_of_ne_zero _ h, conjugation_mul_self_of_ne_zero _ hx5,
        CharTwo.add_self_eq_zero] at hn
      exact zero_ne_one hn
    let A := pairSwap 4 5 (by decide) (x 5) hx5
    refine ⟨A, unitaryTransvection_mem _ _, ?_, ?_⟩
    · intro j hj
      apply transvection_fixes_basis
      have hj4 : j ≠ 4 := by omega
      have hj5 : j ≠ 5 := by omega
      simp [basisVector, hj4, hj5]
    · ext k
      fin_cases k <;> simp [A, pairSwap_apply, basisVector, hx0, hx1, hx2, hx3, hx4,
        conjugation_mul_self_of_ne_zero _ hx5]

private theorem matrix_column (A : form.specialSubgroup) (i j : Fin 6) :
    (A.val • basisVector j) i = A.val.val i j := by
  change (A.val.val *ᵥ Pi.single j 1) i = _
  simp

private theorem eq_one_of_fixes_five (A : form.specialSubgroup)
    (hfix : ∀ j : Fin 6, j.val < 5 → A.val • basisVector j = basisVector j) : A = 1 := by
  have hcol (i j : Fin 6) (hj : j.val < 5) :
      A.val.val i j = basisVector j i := by
    rw [← matrix_column, hfix j hj]
  have hlast (i : Fin 6) (hi : i.val < 5) : A.val.val i 5 = 0 := by
    rw [← matrix_column]
    exact smul_basis_coordinate_eq_zero A i 5 (hfix i hi) (by omega)
  have hm : A.val.val = diagonal ![1, 1, 1, 1, 1, A.val.val 5 5] := by
    ext i j
    by_cases hj : j.val < 5
    · rw [hcol i j hj]
      fin_cases i <;> fin_cases j <;> simp [basisVector]
      norm_num at hj
    · have hj5 : j = 5 := by omega
      subst j
      by_cases hi : i.val < 5
      · rw [hlast i hi]
        have hi5 : i ≠ 5 := by omega
        simp [hi5]
      · have hi5 : i = 5 := by omega
        subst i
        simp
  have hd : A.val.val.det = 1 := by
    have h := ((form.mem_specialSubgroup_iff A.val).mp A.property).2
    simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
      congrArg (fun u : Fieldˣ => u.val) h
  have h55 : A.val.val 5 5 = 1 := by
    rw [hm, det_diagonal] at hd
    simpa [Fin.prod_univ_succ] using hd
  apply Subtype.ext
  apply Units.ext
  change A.val.val = 1
  rw [hm, h55]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem fix_next_column (i : Fin 6)
    (hred : ∀ x : Vector, hermitianNorm x = 1 →
      (∀ j : Fin 6, j.val < i.val → x j = 0) →
      ∃ B : form.specialSubgroup, B ∈ generatedSpecial ∧
        (∀ j : Fin 6, j.val < i.val → B.val • basisVector j = basisVector j) ∧
        B.val • x = basisVector i)
    (A : form.specialSubgroup)
    (hfix : ∀ j : Fin 6, j.val < i.val → A.val • basisVector j = basisVector j) :
    ∃ B : form.specialSubgroup, B ∈ generatedSpecial ∧
      ∀ j : Fin 6, j.val < i.val + 1 → (B * A).val • basisVector j = basisVector j := by
  obtain ⟨B, hB, hBfix, hBA⟩ := hred (A.val • basisVector i)
    ((hermitianNorm_mulVec A _).trans (basisVector_norm i)) (by
      intro j hj
      exact smul_basis_coordinate_eq_zero A j i (hfix j hj) (by omega))
  refine ⟨B, hB, ?_⟩
  intro j hj
  by_cases hji : j = i
  · subst j
    simpa only [Subgroup.coe_mul, mul_smul] using hBA
  · have hjlt : j.val < i.val := by omega
    rw [Subgroup.coe_mul, mul_smul, hfix j hjlt, hBfix j hjlt]

/-- The literal embedded SU₄ is contained in the inverse image of the
projective subgroup generated by the specified isotropic transvections. -/
theorem fourSpaceGeneration : FourSpaceGeneration := by
  intro A hA0 hA1
  have hAfix : ∀ j : Fin 6, j.val < 2 → A.val • basisVector j = basisVector j := by
    intro j hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl <;> assumption
  obtain ⟨B, hB, hBA⟩ := fix_next_column 2 (fun x hx hxprev => by
    obtain ⟨y, hy, hxy, hy2, hyprev⟩ := exists_perpendicular_unit 2 (by decide) x
    exact reduction_of_perpendicular 2 x y hx hy hxy hy2 hxprev hyprev) A hAfix
  obtain ⟨C, hC, hCBA⟩ := fix_next_column 3 three_tail_reduction (B * A) hBA
  obtain ⟨D, hD, hDCBA⟩ := fix_next_column 4 two_tail_reduction (C * (B * A)) hCBA
  have hf : D * (C * (B * A)) ∈ generatedSpecial := by
    rw [eq_one_of_fixes_five _ hDCBA]
    exact generatedSpecial.one_mem
  exact (generatedSpecial.mul_mem_cancel_left hB).mp
    ((generatedSpecial.mul_mem_cancel_left hC).mp
      ((generatedSpecial.mul_mem_cancel_left hD).mp hf))

end Theory.SpecificGroups.U6Two.Generation
