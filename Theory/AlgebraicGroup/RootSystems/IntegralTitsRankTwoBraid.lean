module

public import Theory.AlgebraicGroup.RootSystems.IntegralGeckConstruction
public import Theory.AlgebraicGroup.RootSystems.RankTwoBraid

/-!
# Integral rank-two Tits braid relations

For a finite reduced crystallographic root pairing with a chosen base, this module proves
that the concrete integral Tits matrices of `IntegralGeckConstruction` satisfy every
rank-two Coxeter braid relation.  No irreducibility hypothesis is used, so the result also
applies when the two simple roots lie in different components; the coincident-index case is
handled directly.

On Cartan basis vectors the proof evaluates the alternating products from the Cartan matrix.
On a root line, reflection invariance of root strings moves each `chainBotCoeff` across the
successive reflections.  In the crystallographic rank-two cases of orders `2`, `3`, `4`, and
`6`, the resulting products of signs agree after the corresponding root-reflection identities.
The abstract rank-two braid theorem identifies the final root index, and extensionality on the
sum-indexed basis gives equality of the integral matrices.

This is the braid half of integral Tits coherence, complementing the separate cancellation
correction.  Its mathematical input is the standard crystallographic rank-two Cartan
classification and the root-string description of the Geck--Tits action.
-/

namespace RootPairing.IntegralGeckConstruction

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private lemma linearIndependent_reflectionPerm_iff (i j k : ι) :
    LinearIndependent R ![P.root (P.reflectionPerm i j),
      P.root (P.reflectionPerm i k)] ↔
      LinearIndependent R ![P.root j, P.root k] := by
  rw [RootPairing.IsReduced.linearIndependent_iff P,
    RootPairing.IsReduced.linearIndependent_iff P]
  constructor
  · rintro ⟨hjk, hneg⟩
    constructor
    · intro h
      exact hjk (congrArg (P.reflectionPerm i) h)
    · intro h
      apply hneg
      rw [P.root_reflectionPerm, P.root_reflectionPerm, h, map_neg]
  · rintro ⟨hjk, hneg⟩
    constructor
    · exact (P.reflectionPerm i).injective.ne hjk
    · intro h
      apply hneg
      apply (P.reflection i).injective
      simpa only [P.root_reflectionPerm, map_neg] using h

private lemma chainBotCoeff_reflectionPerm_both (i j k : ι) :
    P.chainBotCoeff (P.reflectionPerm i j) (P.reflectionPerm i k) =
      P.chainBotCoeff j k := by
  have hlin := linearIndependent_reflectionPerm_iff (P := P) i j k
  by_cases h : LinearIndependent R ![P.root j, P.root k]
  · have h' := hlin.mpr h
    apply le_antisymm
    · rw [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h]
      have hmem := (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h').mpr le_rfl
      simpa only [P.root_reflectionPerm, map_sub, map_nsmul,
        P.reflection_same] using P.mapsTo_reflection_root i hmem
    · rw [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h']
      have hmem := (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h).mpr le_rfl
      simpa only [P.root_reflectionPerm, map_sub, map_nsmul] using
        P.mapsTo_reflection_root i hmem
  · have h' : ¬ LinearIndependent R ![P.root (P.reflectionPerm i j),
        P.root (P.reflectionPerm i k)] := fun h' => h (hlin.mp h')
    rw [P.chainBotCoeff_of_not_linearIndependent h,
      P.chainBotCoeff_of_not_linearIndependent h']

private lemma chainBotCoeff_move_reflection (i j k : ι) :
    P.chainBotCoeff j (P.reflectionPerm i k) =
      P.chainBotCoeff (P.reflectionPerm i j) k := by
  symm
  simpa using chainBotCoeff_reflectionPerm_both (P := P) i j
    (P.reflectionPerm i k)

private lemma pairing_eq_cast_of_cartan_eq
    (b : P.Base) {i j : b.support} {z : ℤ}
    (hij : b.cartanMatrix i j = z) :
    P.pairing i j = algebraMap ℤ R z := by
  rw [← P.algebraMap_pairingIn ℤ]
  change P.pairingIn ℤ i j = z at hij
  simpa using congrArg (algebraMap ℤ R) hij

private lemma titsWordSign_order_two (i j : b.support)
    (hij : b.cartanMatrix i j = 0)
    (hji : b.cartanMatrix j i = 0) (k : ι) :
    titsWordSign [i, j] k = titsWordSign [j, i] k := by
  have hfixji : P.reflectionPerm j i = i :=
    P.reflectionPerm_eq_of_pairing_eq_zero
      (b.cartanMatrix_apply_eq_zero_iff_pairing.mp hij)
  have hfixij : P.reflectionPerm i j = j :=
    P.reflectionPerm_eq_of_pairing_eq_zero
      (b.cartanMatrix_apply_eq_zero_iff_pairing.mp hji)
  simp only [titsWordSign, reflectionWord, one_mul]
  rw [chainBotCoeff_move_reflection, chainBotCoeff_move_reflection,
    hfixji, hfixij]
  ac_rfl

private lemma reflectionPerm_eq_of_cartan_neg_one_neg_one (i j : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -1) :
    P.reflectionPerm j i = P.reflectionPerm i j := by
  apply P.root.injective
  rw [P.root_reflectionPerm, P.root_reflectionPerm,
    P.reflection_apply_root' ℤ, P.reflection_apply_root' ℤ]
  change P.pairingIn ℤ i j = -1 at hij
  change P.pairingIn ℤ j i = -1 at hji
  rw [hij, hji]
  module

private lemma titsWordSign_order_three (i j : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -1) (k : ι) :
    titsWordSign [j, i, j] k = titsWordSign [i, j, i] k := by
  have hmiddle := reflectionPerm_eq_of_cartan_neg_one_neg_one
    (P := P) i j hij hji
  simp only [titsWordSign, reflectionWord, one_mul]
  simp only [chainBotCoeff_move_reflection]
  rw [hmiddle, P.reflectionPerm_self, ← hmiddle, P.reflectionPerm_self]
  ac_rfl

private lemma reflectionPerm_fixed_pair_of_cartan_neg_one_neg_two
    (i j : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -2) :
    P.reflectionPerm i (P.reflectionPerm j i) = P.reflectionPerm j i ∧
      P.reflectionPerm j (P.reflectionPerm i j) = P.reflectionPerm i j := by
  constructor <;> apply P.root.injective
  · rw [P.root_reflectionPerm, P.root_reflectionPerm,
      P.reflection_apply, P.reflection_apply, map_sub, map_smul]
    simp only [P.root_coroot'_eq_pairing, P.pairing_same]
    rw [pairing_eq_cast_of_cartan_eq b hij,
      pairing_eq_cast_of_cartan_eq b hji]
    module
  · rw [P.root_reflectionPerm, P.root_reflectionPerm,
      P.reflection_apply, P.reflection_apply, map_sub, map_smul]
    simp only [P.root_coroot'_eq_pairing, P.pairing_same]
    rw [pairing_eq_cast_of_cartan_eq b hij,
      pairing_eq_cast_of_cartan_eq b hji]
    module

private lemma titsWordSign_order_four (i j : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -2) (k : ι) :
    titsWordSign [i, j, i, j] k =
      titsWordSign [j, i, j, i] k := by
  obtain ⟨hfixI, hfixJ⟩ :=
    reflectionPerm_fixed_pair_of_cartan_neg_one_neg_two
      (P := P) i j hij hji
  simp only [titsWordSign, reflectionWord, one_mul]
  simp only [chainBotCoeff_move_reflection]
  rw [hfixI, hfixJ, P.reflectionPerm_self, P.reflectionPerm_self]
  ac_rfl

private lemma reflectionPerm_fixed_triple_of_cartan_neg_one_neg_three
    (i j : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -3) :
    P.reflectionPerm j
        (P.reflectionPerm i (P.reflectionPerm j i)) =
      P.reflectionPerm i (P.reflectionPerm j i) ∧
    P.reflectionPerm i
        (P.reflectionPerm j (P.reflectionPerm i j)) =
      P.reflectionPerm j (P.reflectionPerm i j) := by
  constructor <;> apply P.root.injective
  · rw [P.root_reflectionPerm, P.root_reflectionPerm,
      P.root_reflectionPerm, P.reflection_apply, P.reflection_apply,
      P.reflection_apply, map_sub, map_sub, map_smul, map_smul]
    simp only [P.root_coroot'_eq_pairing, P.pairing_same]
    rw [pairing_eq_cast_of_cartan_eq b hij,
      pairing_eq_cast_of_cartan_eq b hji]
    simp only [map_sub, map_smul, P.root_coroot'_eq_pairing,
      P.pairing_same]
    rw [pairing_eq_cast_of_cartan_eq b hij]
    module
  · rw [P.root_reflectionPerm, P.root_reflectionPerm,
      P.root_reflectionPerm, P.reflection_apply, P.reflection_apply,
      P.reflection_apply, map_sub, map_sub, map_smul, map_smul]
    simp only [P.root_coroot'_eq_pairing, P.pairing_same]
    rw [pairing_eq_cast_of_cartan_eq b hij,
      pairing_eq_cast_of_cartan_eq b hji]
    simp only [map_sub, map_smul, P.root_coroot'_eq_pairing,
      P.pairing_same]
    rw [pairing_eq_cast_of_cartan_eq b hji]
    module

private lemma titsWordSign_order_six (i j : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -3) (k : ι) :
    titsWordSign [i, j, i, j, i, j] k =
      titsWordSign [j, i, j, i, j, i] k := by
  obtain ⟨hfixJ, hfixI⟩ :=
    reflectionPerm_fixed_triple_of_cartan_neg_one_neg_three
      (P := P) i j hij hji
  simp only [titsWordSign, reflectionWord, one_mul]
  simp only [chainBotCoeff_move_reflection]
  rw [hfixJ, hfixI]
  simp only [P.reflectionPerm_self]
  ac_rfl

/-- The two rank-two braid words accumulate the same sign on every root line. -/
public theorem titsWordSign_braidWord_eq_of_orders
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (i j : b.support) (k : ι) :
    titsWordSign (CoxeterSystem.braidWord C i j) k =
      titsWordSign (CoxeterSystem.braidWord C j i) k := by
  by_cases hij : i = j
  · subst j
    rfl
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
        (Theory.AlgebraicGroup.simpleReflection_mul_order_eq_two_of_cartan_zero
          b i j h0.1)
    have horder' : C j i = 2 := by simpa [C.symmetric i j] using horder
    change titsWordSign
        (CoxeterSystem.alternatingWord i j (C i j)) k =
      titsWordSign (CoxeterSystem.alternatingWord j i (C j i)) k
    rw [horder, horder']
    exact titsWordSign_order_two i j h0.1 h0.2 k
  · have horder : C i j = 3 :=
      (hC i j).trans
        (Theory.AlgebraicGroup.simpleReflection_mul_order_eq_three_of_cartan_neg_one_neg_one
          b i j h11.1 h11.2)
    have horder' : C j i = 3 := by simpa [C.symmetric i j] using horder
    change titsWordSign
        (CoxeterSystem.alternatingWord i j (C i j)) k =
      titsWordSign (CoxeterSystem.alternatingWord j i (C j i)) k
    rw [horder, horder']
    exact titsWordSign_order_three i j h11.1 h11.2 k
  · have horder : C i j = 4 :=
      (hC i j).trans
        (Theory.AlgebraicGroup.simpleReflection_mul_order_eq_four_of_cartan_neg_one_neg_two
          b i j h12.1 h12.2)
    have horder' : C j i = 4 := by simpa [C.symmetric i j] using horder
    change titsWordSign
        (CoxeterSystem.alternatingWord i j (C i j)) k =
      titsWordSign (CoxeterSystem.alternatingWord j i (C j i)) k
    rw [horder, horder']
    exact titsWordSign_order_four i j h12.1 h12.2 k
  · have horder : C i j = 4 :=
      (hC i j).trans
        (Theory.AlgebraicGroup.simpleReflection_mul_order_eq_four_of_cartan_neg_two_neg_one
          b i j h21.1 h21.2)
    have horder' : C j i = 4 := by simpa [C.symmetric i j] using horder
    change titsWordSign
        (CoxeterSystem.alternatingWord i j (C i j)) k =
      titsWordSign (CoxeterSystem.alternatingWord j i (C j i)) k
    rw [horder, horder']
    exact (titsWordSign_order_four j i h21.2 h21.1 k).symm
  · have horder : C i j = 6 :=
      (hC i j).trans
        (Theory.AlgebraicGroup.simpleReflection_mul_order_eq_six_of_cartan_neg_one_neg_three
          b i j h13.1 h13.2)
    have horder' : C j i = 6 := by simpa [C.symmetric i j] using horder
    change titsWordSign
        (CoxeterSystem.alternatingWord i j (C i j)) k =
      titsWordSign (CoxeterSystem.alternatingWord j i (C j i)) k
    rw [horder, horder']
    exact titsWordSign_order_six i j h13.1 h13.2 k
  · have horder : C i j = 6 :=
      (hC i j).trans
        (Theory.AlgebraicGroup.simpleReflection_mul_order_eq_six_of_cartan_neg_three_neg_one
          b i j h31.1 h31.2)
    have horder' : C j i = 6 := by simpa [C.symmetric i j] using horder
    change titsWordSign
        (CoxeterSystem.alternatingWord i j (C i j)) k =
      titsWordSign (CoxeterSystem.alternatingWord j i (C j i)) k
    rw [horder, horder']
    exact (titsWordSign_order_six j i h31.2 h31.1 k).symm

private lemma titsWord_mulVec_u_order_two (i j k : b.support)
    (hij : b.cartanMatrix i j = 0)
    (hji : b.cartanMatrix j i = 0) :
    titsWord [i, j] *ᵥ u k = titsWord [j, i] *ᵥ u k := by
  simp only [titsWord, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    titsLift_mulVec_u, Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [show |b.cartanMatrix i j| = 0 by simp [hij],
    show |b.cartanMatrix j i| = 0 by simp [hji]]
  module

private lemma titsWord_mulVec_u_order_three (i j k : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -1) :
    titsWord [j, i, j] *ᵥ u k = titsWord [i, j, i] *ᵥ u k := by
  simp only [titsWord, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    titsLift_mulVec_u, Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [show |b.cartanMatrix i j| = 1 by simp [hij],
    show |b.cartanMatrix j i| = 1 by simp [hji]]
  simp only [show |b.cartanMatrix i i| = 2 by simp,
    show |b.cartanMatrix j j| = 2 by simp]
  module

private lemma titsWord_mulVec_u_order_four (i j k : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -2) :
    titsWord [i, j, i, j] *ᵥ u k =
      titsWord [j, i, j, i] *ᵥ u k := by
  simp only [titsWord, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    titsLift_mulVec_u, Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [show |b.cartanMatrix i j| = 1 by simp [hij],
    show |b.cartanMatrix j i| = 2 by simp [hji]]
  simp only [show |b.cartanMatrix i i| = 2 by simp,
    show |b.cartanMatrix j j| = 2 by simp]
  module

private lemma titsWord_mulVec_u_order_six (i j k : b.support)
    (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -3) :
    titsWord [i, j, i, j, i, j] *ᵥ u k =
      titsWord [j, i, j, i, j, i] *ᵥ u k := by
  simp only [titsWord, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    titsLift_mulVec_u, Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [show |b.cartanMatrix i j| = 1 by simp [hij],
    show |b.cartanMatrix j i| = 3 by simp [hji]]
  simp only [show |b.cartanMatrix i i| = 2 by simp,
    show |b.cartanMatrix j j| = 2 by simp]
  module

/-- The two rank-two braid words act equally on every Cartan basis vector. -/
public theorem titsWord_mulVec_u_braidWord_eq_of_orders
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (i j k : b.support) :
    titsWord (CoxeterSystem.braidWord C i j) *ᵥ u k =
      titsWord (CoxeterSystem.braidWord C j i) *ᵥ u k := by
  by_cases hij : i = j
  · subst j
    rfl
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
        (Theory.AlgebraicGroup.simpleReflection_mul_order_eq_two_of_cartan_zero
          b i j h0.1)
    have horder' : C j i = 2 := by simpa [C.symmetric i j] using horder
    change titsWord (CoxeterSystem.alternatingWord i j (C i j)) *ᵥ u k =
      titsWord (CoxeterSystem.alternatingWord j i (C j i)) *ᵥ u k
    rw [horder, horder']
    exact titsWord_mulVec_u_order_two i j k h0.1 h0.2
  · have horder : C i j = 3 :=
      (hC i j).trans
        (Theory.AlgebraicGroup.simpleReflection_mul_order_eq_three_of_cartan_neg_one_neg_one
          b i j h11.1 h11.2)
    have horder' : C j i = 3 := by simpa [C.symmetric i j] using horder
    change titsWord (CoxeterSystem.alternatingWord i j (C i j)) *ᵥ u k =
      titsWord (CoxeterSystem.alternatingWord j i (C j i)) *ᵥ u k
    rw [horder, horder']
    exact titsWord_mulVec_u_order_three i j k h11.1 h11.2
  · have horder : C i j = 4 :=
      (hC i j).trans
        (Theory.AlgebraicGroup.simpleReflection_mul_order_eq_four_of_cartan_neg_one_neg_two
          b i j h12.1 h12.2)
    have horder' : C j i = 4 := by simpa [C.symmetric i j] using horder
    change titsWord (CoxeterSystem.alternatingWord i j (C i j)) *ᵥ u k =
      titsWord (CoxeterSystem.alternatingWord j i (C j i)) *ᵥ u k
    rw [horder, horder']
    exact titsWord_mulVec_u_order_four i j k h12.1 h12.2
  · have horder : C i j = 4 :=
      (hC i j).trans
        (Theory.AlgebraicGroup.simpleReflection_mul_order_eq_four_of_cartan_neg_two_neg_one
          b i j h21.1 h21.2)
    have horder' : C j i = 4 := by simpa [C.symmetric i j] using horder
    change titsWord (CoxeterSystem.alternatingWord i j (C i j)) *ᵥ u k =
      titsWord (CoxeterSystem.alternatingWord j i (C j i)) *ᵥ u k
    rw [horder, horder']
    exact (titsWord_mulVec_u_order_four j i k h21.2 h21.1).symm
  · have horder : C i j = 6 :=
      (hC i j).trans
        (Theory.AlgebraicGroup.simpleReflection_mul_order_eq_six_of_cartan_neg_one_neg_three
          b i j h13.1 h13.2)
    have horder' : C j i = 6 := by simpa [C.symmetric i j] using horder
    change titsWord (CoxeterSystem.alternatingWord i j (C i j)) *ᵥ u k =
      titsWord (CoxeterSystem.alternatingWord j i (C j i)) *ᵥ u k
    rw [horder, horder']
    exact titsWord_mulVec_u_order_six i j k h13.1 h13.2
  · have horder : C i j = 6 :=
      (hC i j).trans
        (Theory.AlgebraicGroup.simpleReflection_mul_order_eq_six_of_cartan_neg_three_neg_one
          b i j h31.1 h31.2)
    have horder' : C j i = 6 := by simpa [C.symmetric i j] using horder
    change titsWord (CoxeterSystem.alternatingWord i j (C i j)) *ᵥ u k =
      titsWord (CoxeterSystem.alternatingWord j i (C j i)) *ᵥ u k
    rw [horder, horder']
    exact (titsWord_mulVec_u_order_six j i k h31.2 h31.1).symm

private lemma root_reflectionWord (word : List b.support) (k : ι) :
    P.root (reflectionWord word k) = b.wordProd word • P.root k := by
  induction word with
  | nil => simp [reflectionWord, b.wordProd_nil]
  | cons i word ih =>
      rw [reflectionWord, P.root_reflectionPerm, ih, b.wordProd_cons,
        mul_smul]
      rfl

private lemma reflectionWord_eq_of_wordProd_eq
    {word word' : List b.support} (h : b.wordProd word = b.wordProd word')
    (k : ι) : reflectionWord word k = reflectionWord word' k := by
  apply P.root.injective
  rw [root_reflectionWord, root_reflectionWord, h]

/-- The two rank-two braid words act equally on every root-line basis vector. -/
public theorem titsWord_mulVec_v_braidWord_eq_of_orders
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (i j : b.support) (k : ι) :
    letI := P.indexNeg
    titsWord (CoxeterSystem.braidWord C i j) *ᵥ v k =
      titsWord (CoxeterSystem.braidWord C j i) *ᵥ v k := by
  let := P.indexNeg
  rw [titsWord_mulVec_v, titsWord_mulVec_v,
    titsWordSign_braidWord_eq_of_orders C hC i j k]
  congr 2
  exact reflectionWord_eq_of_wordProd_eq
    (b.wordProd_braidWord_eq_of_orders C hC i j) k

/-- The concrete integral Tits matrices satisfy every rank-two Coxeter braid relation. -/
public theorem titsWord_braidWord_eq_of_orders
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (i j : b.support) :
    titsWord (CoxeterSystem.braidWord C i j) =
      titsWord (CoxeterSystem.braidWord C j i) := by
  let := P.indexNeg
  ext row column
  cases column with
  | inl k =>
      have h := congrFun
        (titsWord_mulVec_u_braidWord_eq_of_orders C hC i j k) row
      simpa [u, Matrix.mulVec_single] using h
  | inr k =>
      have h := congrFun
        (titsWord_mulVec_v_braidWord_eq_of_orders C hC i j k) row
      simpa [v, Matrix.mulVec_single] using h

end
end RootPairing.IntegralGeckConstruction
