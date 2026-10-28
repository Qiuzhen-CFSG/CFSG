module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.Basic
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.Normalization
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Perm.Fin
/-!
# Orthogonality of frames preserved by nonabelian odd unitary groups

The permutation image on three independent projective lines has order dividing
three. Nonabelianness makes this image nontrivial. The diagonal kernel separates
every pair of coordinates: otherwise a three-cycle propagates equality of two
characters to all three, making the kernel central and the group abelian.

For an invariant Hermitian matrix, two nonzero entries in one row would identify
two diagonal characters. Thus every row has at most one nonzero entry. Hermitian
symmetry and the three-cycle now exclude every off-diagonal entry. This works
for arbitrary odd subgroups, without a norm-one condition on their diagonal
characters or a nonabelian three-subgroup.

Finite-field norm surjectivity then normalizes the same projective lines. The
consumers place any line-preserving overgroup in the actual frame stabilizer and
frame-torus normalizer. Existence of the supplied linear frame remains the
separate geometric premise in the assembly of GLS4, Chapter 4, Lemma 3.11(a).

Source: `refs/KGroup/GLS4/Chapter4.tex`, lines 585–603. The coordinate action,
separation argument and change-of-basis calculation adapt the repository's
`CFSG/Quasithin/Chapter1/Section03/Embeddings/InvariantThree/OddClassical/UnitaryThree/ModTwoExtraspecial/Placement/OrthogonalFrames.lean`.
The row-support argument replaces that proof's three-power norm calculation.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
open scoped Pointwise LinearAlgebra.Projectivization
namespace UnitaryThree.OddTorusNormalizer.NonabelianFrame

namespace GramDiagonal
variable {E G : Type*} [Field E] [Group G]
variable (r : G →* GL (Fin 3) E)
variable (hm : ∀ g, r g • Set.range (coordinateLine (E := E)) = Set.range coordinateLine)
include hm

private theorem column_support (g : G) (i : Fin 3) :
    ∃ j : Fin 3, (r g).val j i ≠ 0 ∧
      ∀ k : Fin 3, k ≠ j → (r g).val k i = 0 := by
  have hi := Set.smul_mem_smul_set (a := r g)
    (Set.mem_range_self (f := coordinateLine (E := E)) i)
  rw [hm] at hi
  obtain ⟨j, hj⟩ := hi
  have hj' := hj.symm
  rw [coordinateLine, coordinateLine, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff] at hj'
  obtain ⟨a, ha⟩ := hj'
  have he (k : Fin 3) : (a : E) * (Pi.single j 1 : Fin 3 → E) k = (r g).val k i := by
    have h := congrFun ha k
    change (a : E) * (Pi.single j 1 : Fin 3 → E) k =
      ((r g).val *ᵥ Pi.single i 1) k at h
    simpa only [mulVec_single_one, col_apply] using h
  refine ⟨j, ?_, ?_⟩
  · have hjj : (a : E) = (r g).val j i := by simpa only [Pi.single_eq_same, mul_one] using he j
    exact hjj ▸ Units.ne_zero a
  · intro k hkj
    simpa only [Pi.single_apply, if_neg hkj, mul_zero] using (he k).symm

private noncomputable def columnIndex (g : G) (i : Fin 3) : Fin 3 :=
  (column_support r hm g i).choose

private theorem columnIndex_spec (g : G) (i : Fin 3) :
    (r g).val (columnIndex r hm g i) i ≠ 0 ∧
      ∀ k : Fin 3, k ≠ columnIndex r hm g i → (r g).val k i = 0 :=
  (column_support r hm g i).choose_spec

private theorem columnIndex_eq_of_ne_zero (g : G) (i j : Fin 3)
    (h : (r g).val j i ≠ 0) : columnIndex r hm g i = j := by
  by_contra hne
  exact h ((columnIndex_spec r hm g i).2 j (Ne.symm hne))

private theorem columnIndex_one (i : Fin 3) : columnIndex r hm 1 i = i := by
  apply columnIndex_eq_of_ne_zero r hm
  simp

private theorem mul_entry (x y : G) (k i : Fin 3) :
    (r (x * y)).val k i =
      (r x).val k (columnIndex r hm y i) * (r y).val (columnIndex r hm y i) i := by
  rw [map_mul]
  change ((r x).val * (r y).val) k i = _
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single (columnIndex r hm y i)
  · intro j _ hj
    rw [(columnIndex_spec r hm y i).2 j hj, mul_zero]
  · simp

private theorem columnIndex_mul (x y : G) (i : Fin 3) :
    columnIndex r hm (x * y) i = columnIndex r hm x (columnIndex r hm y i) := by
  apply columnIndex_eq_of_ne_zero r hm
  rw [mul_entry r hm]
  exact mul_ne_zero (columnIndex_spec r hm x (columnIndex r hm y i)).1
    (columnIndex_spec r hm y i).1

private noncomputable def coordinatePermutation (x : G) : Equiv.Perm (Fin 3) where
  toFun := columnIndex r hm x
  invFun := columnIndex r hm x⁻¹
  left_inv i := by rw [← columnIndex_mul, inv_mul_cancel, columnIndex_one]
  right_inv i := by rw [← columnIndex_mul, mul_inv_cancel, columnIndex_one]

private noncomputable def coordinateAction : G →* Equiv.Perm (Fin 3) where
  toFun := coordinatePermutation r hm
  map_one' := Equiv.ext (columnIndex_one r hm)
  map_mul' x y := Equiv.ext (columnIndex_mul r hm x y)

private theorem coordinateAction_ker (g : G) :
    coordinateAction r hm g = 1 ↔ (r g).val.IsDiag := by
  constructor
  · intro hx
    have hfix (i : Fin 3) : columnIndex r hm g i = i :=
      congrArg (fun p : Equiv.Perm (Fin 3) => p i) hx
    intro i j hij
    exact (columnIndex_spec r hm g j).2 i (by simpa only [hfix] using hij)
  · intro hx
    apply Equiv.ext
    intro i
    change columnIndex r hm g i = i
    by_contra hne
    exact (columnIndex_spec r hm g i).1 (hx hne)

private theorem range_card_dvd_three (hG : Odd (Nat.card G)) :
    Nat.card (coordinateAction r hm).range ∣ 3 := by
  let f := coordinateAction r hm
  have hd : Nat.card f.range ∣ 6 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, show Nat.factorial 3 = 6 from rfl] using
      f.range.card_subgroup_dvd_card
  have ho : Odd (Nat.card f.range) := hG.of_dvd_nat (Subgroup.card_range_dvd f)
  exact ho.coprime_two_right.dvd_mul_left.mp hd

private theorem diagonal_conjugate (g a : G)
    (ha : (r a).val.IsDiag) (hga : (r (g * a * g⁻¹)).val.IsDiag) (i : Fin 3) :
    (r (g * a * g⁻¹)).val (coordinateAction r hm g i) (coordinateAction r hm g i) =
      (r a).val i i := by
  have he : r (g * a * g⁻¹) * r g = r g * r a := by
    simp only [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one]
  have hh := congrArg (fun x : GL (Fin 3) E => x.val (coordinateAction r hm g i) i) he
  change ((r (g * a * g⁻¹)).val * (r g).val) _ _ = ((r g).val * (r a).val) _ _ at hh
  rw [← ha.diagonal_diag, ← hga.diagonal_diag] at hh
  simp only [diagonal_mul, mul_diagonal, diag_apply] at hh
  exact (mul_right_cancel₀ (columnIndex_spec r hm g i).1)
    (hh.trans (mul_comm _ _))

omit hm in
set_option synthInstance.maxSize 512 in
private theorem pair_cycle (s : Equiv.Perm (Fin 3)) (hs : s ^ 3 = 1) (hn : s ≠ 1)
    (i j : Fin 3) (hij : i ≠ j) (k : Fin 3) :
    k = i ∨ k = j ∨
      (k = s i ∧ (s j = i ∨ s j = j)) ∨ (k = s j ∧ (s i = i ∨ s i = j)) := by
  have h : ∀ (s : Equiv.Perm (Fin 3)), s ^ 3 = 1 → s ≠ 1 →
      ∀ i j : Fin 3, i ≠ j → ∀ k : Fin 3,
      k = i ∨ k = j ∨
        (k = s i ∧ (s j = i ∨ s j = j)) ∨ (k = s j ∧ (s i = i ∨ s i = j)) := by decide +kernel
  exact h s hs hn i j hij k

private theorem exists_moving (hr : Function.Injective r) (hn : ¬ IsMulCommutative G) :
    ∃ g : G, coordinateAction r hm g ≠ 1 := by
  let f := coordinateAction r hm
  have hdiag (a : G) : f a = 1 ↔ (r a).val.IsDiag := coordinateAction_ker r hm a
  by_contra! h
  apply hn
  refine ⟨⟨fun a b => hr ?_⟩⟩
  rw [map_mul, map_mul]
  apply Units.ext
  change (r a).val * (r b).val = (r b).val * (r a).val
  rw [← ((hdiag a).mp (h a)).diagonal_diag, ← ((hdiag b).mp (h b)).diagonal_diag,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext k
  exact mul_comm _ _

private theorem separating_diagonal (hr : Function.Injective r)
    (hG : Odd (Nat.card G)) (hn : ¬ IsMulCommutative G)
    (i j : Fin 3) (hij : i ≠ j) :
    ∃ a : G, (r a).val.IsDiag ∧ (r a).val i i ≠ (r a).val j j := by
  classical
  let f := coordinateAction r hm
  have hdiag (a : G) : f a = 1 ↔ (r a).val.IsDiag := coordinateAction_ker r hm a
  obtain ⟨g, hg⟩ := exists_moving r hm hr hn
  have hfcard : Nat.card f.range ∣ 3 := range_card_dvd_three r hm hG
  have hfcube : (f g) ^ 3 = 1 := by
    have h := orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_natCard (f.rangeRestrict g)).trans hfcard)
    exact congrArg Subtype.val h
  by_contra! hsame
  have hker : f.ker ≤ Subgroup.center G := by
    intro a ha
    have hfa : f a = 1 := ha
    have haD := (hdiag a).mp hfa
    let b := g⁻¹ * a * g
    have hfb : f b = 1 := by simp [b, map_mul, map_inv, hfa]
    have hbD := (hdiag b).mp hfb
    have hgb : g * b * g⁻¹ = a := by simp [b, mul_assoc]
    have hrot : (r a).val (f g i) (f g i) = (r a).val (f g j) (f g j) := by
      have hi := diagonal_conjugate r hm g b hbD (by rwa [hgb]) i
      have hj := diagonal_conjugate r hm g b hbD (by rwa [hgb]) j
      rw [hgb] at hi hj
      exact hi.trans ((hsame b hbD).trans hj.symm)
    have heq (k : Fin 3) : (r a).val k k = (r a).val i i := by
      have he := hsame a haD
      rcases pair_cycle (f g) hfcube hg i j hij k with h | h | ⟨h, h' | h'⟩ | ⟨h, h' | h'⟩
      · rw [h]
      · rw [h, he]
      · rw [h, hrot, h']
      · rw [h, hrot, h', he]
      · rw [h, ← hrot, h']
      · rw [h, ← hrot, h', he]
    have hcentral : r a ∈ Subgroup.center (GL (Fin 3) E) := by
      apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
      refine ⟨(r a).val i i, ?_⟩
      conv_rhs => rw [← haD.diagonal_diag]
      change diagonal (fun _ => (r a).val i i) = diagonal (r a).val.diag
      congr 1
      ext k
      exact (heq k).symm
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply hr
    simpa only [map_mul] using Subgroup.mem_center_iff.mp hcentral (r x)
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic f.range := isCyclic_of_card_dvd_prime hfcard
  exact hn (f.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center
    (by simpa using hker))

private theorem gram_entry (J : HermitianForm 3 E) (A : Matrix (Fin 3) (Fin 3) E)
    (g : G) (i j : Fin 3) :
    (J.conjTranspose (r g).val * A * (r g).val) i j =
      J.conj ((r g).val (coordinateAction r hm g i) i) *
        A (coordinateAction r hm g i) (coordinateAction r hm g j) *
          (r g).val (coordinateAction r hm g j) j := by
  calc
    _ = (J.conjTranspose (r g).val * A) i (coordinateAction r hm g j) *
        (r g).val (coordinateAction r hm g j) j := by
      rw [mul_apply]
      apply Finset.sum_eq_single (coordinateAction r hm g j)
      · intro k _ hk
        rw [(columnIndex_spec r hm g j).2 k hk, mul_zero]
      · simp
    _ = _ := by
      congr 1
      rw [mul_apply]
      apply Finset.sum_eq_single (coordinateAction r hm g i)
      · intro k _ hk
        change J.conj ((r g).val k i) * _ = 0
        rw [(columnIndex_spec r hm g i).2 k hk, map_zero, zero_mul]
      · simp

omit hm in
private theorem adjoint_diagonal (J : HermitianForm 3 E) (d : Fin 3 → E) :
    J.conjTranspose (diagonal d) = diagonal (fun i => J.conj (d i)) := by
  ext i j
  by_cases h : i = j
  · subst j; simp [HermitianForm.conjTranspose]
  · simp [HermitianForm.conjTranspose, diagonal_apply_ne _ h,
      diagonal_apply_ne _ (Ne.symm h)]

private theorem row_unique (hr : Function.Injective r)
    (hG : Odd (Nat.card G)) (hn : ¬ IsMulCommutative G)
    (J : HermitianForm 3 E) (A : Matrix (Fin 3) (Fin 3) E)
    (hA : ∀ g, J.conjTranspose (r g).val * A * (r g).val = A)
    (i j k : Fin 3) (hj : A i j ≠ 0) (hk : A i k ≠ 0) : j = k := by
  by_contra hjk
  obtain ⟨a, haD, hne⟩ := separating_diagonal r hm hr hG hn j k hjk
  have he := hA a
  rw [← haD.diagonal_diag, adjoint_diagonal] at he
  have hc (l : Fin 3) (hl : A i l ≠ 0) :
      J.conj ((r a).val i i) * (r a).val l l = 1 := by
    have heil := congrArg (fun B : Matrix (Fin 3) (Fin 3) E => B i l) he
    simp only [diagonal_mul, mul_diagonal, diag_apply] at heil
    apply mul_right_cancel₀ hl
    calc
      (J.conj ((r a).val i i) * (r a).val l l) * A i l =
          J.conj ((r a).val i i) * A i l * (r a).val l l := by ring
      _ = 1 * A i l := by simpa only [one_mul] using heil
  have hcj := hc j hj
  have hci : J.conj ((r a).val i i) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hcj
    exact zero_ne_one hcj
  exact hne (mul_left_cancel₀ hci (hcj.trans (hc k hk).symm))

omit hm in
set_option synthInstance.maxSize 512 in
private theorem cycle_pair (s : Equiv.Perm (Fin 3)) (hs : s ^ 3 = 1) (hn : s ≠ 1)
    (i j : Fin 3) (hij : i ≠ j) :
    (s i = j ∧ s j ≠ i) ∨ (s j = i ∧ s i ≠ j) := by
  have h : ∀ s : Equiv.Perm (Fin 3), s ^ 3 = 1 → s ≠ 1 →
      ∀ i j : Fin 3, i ≠ j → (s i = j ∧ s j ≠ i) ∨ (s j = i ∧ s i ≠ j) := by
    decide +kernel
  exact h s hs hn i j hij

private theorem invariant_hermitian_isDiag (hr : Function.Injective r)
    (hG : Odd (Nat.card G)) (hn : ¬ IsMulCommutative G)
    (J : HermitianForm 3 E) (A : Matrix (Fin 3) (Fin 3) E)
    (hA : ∀ g, J.conjTranspose (r g).val * A * (r g).val = A)
    (hsym : ∀ i j, J.conj (A j i) = A i j) : A.IsDiag := by
  obtain ⟨g, hg⟩ := exists_moving r hm hr hn
  let f := coordinateAction r hm
  have hfcube : (f g) ^ 3 = 1 := by
    have h := orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_natCard (f.rangeRestrict g)).trans (range_card_dvd_three r hm hG))
    exact congrArg Subtype.val h
  have hswap (i j : Fin 3) (h : A i j ≠ 0) : A j i ≠ 0 := by
    intro hz
    apply h
    rw [← hsym i j, hz, map_zero]
  have hmove (i j : Fin 3) (h : A i j ≠ 0) : A (f g i) (f g j) ≠ 0 := by
    intro hz
    apply h
    have he := gram_entry r hm J A g i j
    rw [hA g, hz, mul_zero, zero_mul] at he
    exact he
  intro i j hij
  by_contra hz
  have hmoved := hmove i j hz
  rcases cycle_pair (f g) hfcube hg i j hij with ⟨hi, hj⟩ | ⟨hj, hi⟩
  · rw [hi] at hmoved
    exact hj (row_unique r hm hr hG hn J A hA j (f g j) i hmoved (hswap i j hz))
  · rw [hj] at hmoved
    exact hi (row_unique r hm hr hG hn J A hA i (f g i) j
      (hswap _ _ hmoved) hz)

end GramDiagonal

variable {E : Type*} [Field E]

private theorem adjoint_mul (J : HermitianForm 3 E) (A B : Matrix (Fin 3) (Fin 3) E) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : E →+* E).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

/-- An arbitrary linear frame preserved by a nonabelian odd special-unitary
subgroup already has diagonal Gram matrix. -/
theorem gram_isDiag_of_nonabelian_odd_preservesLines [Finite E]
    (J : HermitianForm 3 E) (H : Subgroup J.specialSubgroup)
    (hH : Odd (Nat.card H)) (hn : ¬ IsMulCommutative H)
    (C : GL (Fin 3) E) (hpres : PreservesLines J H C) :
    (J.conjTranspose C.val * J.form * C.val).IsDiag := by
  let r : H →* GL (Fin 3) E :=
    { toFun := fun u => C⁻¹ * u.val.val * C
      map_one' := by simp
      map_mul' := fun u v => by simp [mul_assoc] }
  have hr : Function.Injective r := by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    change C⁻¹ * u.val.val * C = C⁻¹ * v.val.val * C at h
    exact mul_left_cancel (mul_right_cancel h)
  have hrm (u : H) : r u • Set.range (coordinateLine (E := E)) =
      Set.range (coordinateLine (E := E)) := by
    change (C⁻¹ * u.val.val * C) • _ = _
    rw [mul_smul, mul_smul, hpres _ u.property, inv_smul_smul]
  let A : Matrix (Fin 3) (Fin 3) E := J.conjTranspose C.val * J.form * C.val
  have hrpres (u : H) : J.conjTranspose (r u).val * A * (r u).val = A := by
    have hC : C.val * (C⁻¹).val = 1 := C.val_inv
    have hpres := ((J.mem_specialSubgroup_iff u.val.val).mp u.val.property).1
    change J.conjTranspose ((C⁻¹).val * u.val.val.val * C.val) *
      (J.conjTranspose C.val * J.form * C.val) *
      ((C⁻¹).val * u.val.val.val * C.val) = _
    rw [adjoint_mul, adjoint_mul]
    calc
      _ = J.conjTranspose C.val *
          (J.conjTranspose u.val.val.val *
            (J.conjTranspose (C⁻¹).val * J.conjTranspose C.val) * J.form *
            (C.val * (C⁻¹).val) * u.val.val.val) * C.val := by simp only [mul_assoc]
      _ = A := by
        rw [← adjoint_mul, hC]
        have hone : J.conjTranspose (1 : Matrix (Fin 3) (Fin 3) E) = 1 := by
          ext i j
          by_cases h : i = j
          · subst j; simp [HermitianForm.conjTranspose]
          · simp [HermitianForm.conjTranspose, h, Ne.symm]
        rw [hone]
        simpa only [mul_one] using congrArg (fun B => J.conjTranspose C.val * B * C.val) hpres

  apply GramDiagonal.invariant_hermitian_isDiag r hrm hr hH hn J A hrpres
  let : Star E := ⟨J.conj⟩
  let : InvolutiveStar E := ⟨J.conj_involutive⟩
  let : StarMul E := ⟨fun r s => by
    change J.conj (r * s) = J.conj s * J.conj r
    rw [map_mul, mul_comm]⟩
  let : StarRing E := ⟨fun r s => by
    change J.conj (r + s) = J.conj r + J.conj s
    rw [map_add]⟩
  have hAherm : A.IsHermitian := by
    apply Matrix.isHermitian_conjTranspose_mul_mul
    exact Matrix.IsHermitian.ext J.form_hermitian
  exact fun i j => hAherm.apply i j

/-- If a line-preserving group contains a nonabelian odd subgroup, its same
three lines can be normalized to an orthogonal frame over the original field.
This discharges the Gram premise in the frame-normalization step of GLS4 3.11(a). -/
theorem specialFrameStabilizer_of_nonabelian_odd_preservesLines [Finite E]
    (J : HermitianForm 3 E) (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (H K : Subgroup J.specialSubgroup) (hHK : H ≤ K)
    (hH : Odd (Nat.card H)) (hn : ¬ IsMulCommutative H)
    (C : GL (Fin 3) E) (hpres : PreservesLines J K C) :
    ∃ P : OrthogonalFrame J, K ≤ specialFrameStabilizer J P := by
  apply specialFrameStabilizer_of_diagonal_gram J q hcard hfixed K C hpres
  exact gram_isDiag_of_nonabelian_odd_preservesLines J H hH hn C
    (fun g hg => hpres g (hHK hg))

/-- The same normalized frame places the whole line-preserving group in the
normalizer of the literal special-unitary frame torus. -/
theorem specialFrameTorus_normalizer_of_nonabelian_odd_preservesLines [Finite E]
    (J : HermitianForm 3 E) (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (H K : Subgroup J.specialSubgroup) (hHK : H ≤ K)
    (hH : Odd (Nat.card H)) (hn : ¬ IsMulCommutative H)
    (C : GL (Fin 3) E) (hpres : PreservesLines J K C) :
    ∃ P : OrthogonalFrame J, K ≤ Subgroup.normalizer (specialFrameTorus J P) := by
  obtain ⟨P, hP⟩ := specialFrameStabilizer_of_nonabelian_odd_preservesLines
    J q hcard hfixed H K hHK hH hn C hpres
  exact ⟨P, hP.trans (specialFrameStabilizer_le_normalizer J P)⟩

end UnitaryThree.OddTorusNormalizer.NonabelianFrame
