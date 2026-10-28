module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement.Frames
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Orthogonalizing an invariant unitary frame

The permutation image of a three-group on three frame lines is cyclic of
order dividing three. Its diagonal kernel cannot consist of scalars: a
central kernel and cyclic image would make the group abelian. Conjugating
by a nonidentity three-cycle then shows that the diagonal kernel separates
every pair of lines.

For a field of order `p²` with `p ≡ 2 (mod 3)`, every field element of
three-power order has Hermitian norm one. Distinct diagonal weights therefore
force the corresponding Gram entry to vanish. Nondegeneracy makes every
diagonal entry nonzero, and finite-field norm surjectivity rescales the basis
to an orthonormal one. Rescaling preserves the original lines and hence their
invariance under the whole subgroup. Neither solvability nor an order bound
on that subgroup, nor exponent three for its three-subgroup, is used.

Source: GLS3, proof of Theorem 6.5.3 around (6.5.1),
`refs/KGroup/GLS3/chapter6.tex`; Aschbacher–Smith, proof of Proposition 1.3.4,
printed p.511 (PDF p.528). The coordinate-action construction adapts
`Theory.SpecificGroups.SU3.OddThreeLocal.Monomial.LocalCore.CoordinateAction`
to the conjugated natural representation before orthogonality is known.
-/

open Matrix BenderSuzuki.MatrixGroups
open HermitianForm.OddThreeLocal.Monomial
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement

namespace OrthogonalFrames.WeightAction
variable {E G : Type*} [Field E] [Group G]
variable (r : G →* GL (Fin 3) E)
variable (hm : ∀ g, r g • coordinateVectors (E := E) = coordinateVectors)
include hm

private theorem column_support (g : G) (i : Fin 3) :
    ∃ j : Fin 3, (r g).val j i ≠ 0 ∧
      ∀ k : Fin 3, k ≠ j → (r g).val k i = 0 := by
  have hi := Set.smul_mem_smul_set (a := r g)
    (single_mem_coordinateVectors i (one_ne_zero : (1 : E) ≠ 0))
  rw [hm] at hi
  change (r g).val *ᵥ Pi.single i 1 ∈ coordinateVectors at hi
  simpa only [Matrix.mulVec_single_one, coordinateVectors, Matrix.col_apply,
    Set.mem_ofPred_eq] using hi

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

private theorem range_card_dvd_three (hG : IsPGroup 3 G) :
    Nat.card (coordinateAction r hm).range ∣ 3 := by
  let f := coordinateAction r hm
  have hd : Nat.card f.range ∣ 6 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, show Nat.factorial 3 = 6 from rfl] using
      f.range.card_subgroup_dvd_card
  obtain ⟨n, hn⟩ := (hG.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_card_eq
  have hn1 : n ≤ 1 := by
    by_contra! h
    have hh := Nat.pow_le_pow_right (by decide : 0 < 3) h
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hd
    rw [hn] at hle
    norm_num at hh
    omega
  change Nat.card f.range ∣ 3
  rw [hn]
  interval_cases n <;> norm_num

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


private theorem separating_diagonal (hr : Function.Injective r)
    (hG : IsPGroup 3 G) (hn : ¬ IsMulCommutative G)
    (i j : Fin 3) (hij : i ≠ j) :
    ∃ a : G, (r a).val.IsDiag ∧ (r a).val i i ≠ (r a).val j j := by
  classical
  let f := coordinateAction r hm
  have hdiag (a : G) : f a = 1 ↔ (r a).val.IsDiag := coordinateAction_ker r hm a
  have hg : ∃ g : G, f g ≠ 1 := by
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
  obtain ⟨g, hg⟩ := hg
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

end OrthogonalFrames.WeightAction

namespace OrthogonalFrames
variable {E : Type*} [Field E]

private theorem norm_one [Finite E] (J : HermitianForm 3 E) (p : ℕ)
    (hp : 1 < p) (hm : p % 3 = 2) (hE : Nat.card E = p ^ 2)
    (hc : ∀ x, J.conj x = x ^ p) (a : E) (n : ℕ) (ha : a ^ (3 ^ n) = 1) :
    J.conj a * a = 1 := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hd3 := orderOf_dvd_of_pow_eq_one ha
  have hcop : Nat.Coprime (orderOf a) (p - 1) := by
    apply Nat.Coprime.of_dvd_left hd3
    apply Nat.Coprime.pow_left
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  have hd : orderOf a ∣ (p - 1) * (p + 1) := by
    let := Fintype.ofFinite E
    have hh := orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one a ha0)
    rw [← Nat.card_eq_fintype_card, hE] at hh
    convert hh using 1
    nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p),
      Nat.sub_add_cancel (by nlinarith : 1 ≤ p ^ 2)]
  have hpow : a ^ (p + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_mul_left.mp hd)
  simpa only [hc, pow_succ] using hpow


private theorem adjoint_mul (J : HermitianForm 3 E) (A B : Matrix (Fin 3) (Fin 3) E) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : E →+* E).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem adjoint_diagonal (J : HermitianForm 3 E) (d : Fin 3 → E) :
    J.conjTranspose (diagonal d) = diagonal (fun i => J.conj (d i)) := by
  ext i j
  by_cases h : i = j
  · subst j; simp [HermitianForm.conjTranspose]
  · simp [HermitianForm.conjTranspose, diagonal_apply_ne _ h,
      diagonal_apply_ne _ (Ne.symm h)]

private theorem normalize [Finite E] (J : HermitianForm 3 E) (p : ℕ)
    (hp : p.Prime) (hE : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (H : Subgroup J.specialSubgroup) (C : GL (Fin 3) E)
    (hframe : PreservesFrame H C)
    (hdiag : (J.conjTranspose C.val * J.form * C.val).IsDiag) :
    HasOrthogonalFrame H := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite E
  let : CharP E p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hE)
  let : Star E := ⟨J.conj⟩
  let : InvolutiveStar E := ⟨J.conj_involutive⟩
  let : StarMul E := ⟨fun r s => by
    change J.conj (r * s) = J.conj s * J.conj r
    rw [map_mul, mul_comm]⟩
  let : StarRing E := ⟨fun r s => by
    change J.conj (r + s) = J.conj r + J.conj s
    rw [map_add]⟩
  let A : Matrix (Fin 3) (Fin 3) E := J.conjTranspose C.val * J.form * C.val
  change A.IsDiag at hdiag
  have hAherm : A.IsHermitian := by
    apply Matrix.isHermitian_conjTranspose_mul_mul
    exact Matrix.IsHermitian.ext J.form_hermitian
  have hAdet : A.det ≠ 0 := by
    change (C.valᴴ * J.form * C.val).det ≠ 0
    rw [det_mul, det_mul, det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr C.det_ne_zero)
      J.form_nondegenerate) C.det_ne_zero
  have ha0 (i : Fin 3) : A i i ≠ 0 := by
    have he := hdiag.diagonal_diag
    change diagonal A.diag = A at he
    rw [← he, det_diagonal] at hAdet
    exact (Finset.prod_ne_zero_iff.mp hAdet) i (Finset.mem_univ i)
  have hs (i : Fin 3) : ∃ d : E, d ≠ 0 ∧ d * J.conj d = (A i i)⁻¹ :=
    J.exists_norm_of_prime_frobenius hc hE _
      (by rw [map_inv₀]; exact congrArg Inv.inv (show J.conj (A i i) = A i i from hAherm.apply i i)) (inv_ne_zero (ha0 i))
  choose d hd0 hd using hs
  let D : GL (Fin 3) E := GeneralLinearGroup.mkOfDetNeZero (diagonal d)
    (by rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hd0 i))
  have hDC : D • HermitianForm.OddThreeLocal.Monomial.coordinateVectors (E := E) =
      HermitianForm.OddThreeLocal.Monomial.coordinateVectors := by
    apply Set.Subset.antisymm
    · apply Set.smul_set_subset_iff.mpr
      rintro v ⟨i, hi, hv⟩
      change diagonal d *ᵥ v ∈ _
      refine ⟨i, ?_, ?_⟩
      · simpa only [mulVec_diagonal] using mul_ne_zero (hd0 i) hi
      · intro j hj
        simp [mulVec_diagonal, hv j hj]
    · intro v hv
      have hv' : (fun i => (d i)⁻¹ * v i) ∈
          HermitianForm.OddThreeLocal.Monomial.coordinateVectors := by
        obtain ⟨i, hi, hz⟩ := hv
        exact ⟨i, mul_ne_zero (inv_ne_zero (hd0 i)) hi, fun j hj => by simp [hz j hj]⟩
      refine ⟨_, hv', ?_⟩
      change diagonal d *ᵥ (fun i => (d i)⁻¹ * v i) = v
      ext i
      simp [mulVec_diagonal, hd0]
  refine ⟨C * D, ?_, ?_⟩
  · change J.conjTranspose (C.val * diagonal d) * J.form * (C.val * diagonal d) = 1
    rw [adjoint_mul, adjoint_diagonal]
    have he : (diagonal (fun i => J.conj (d i)) * J.conjTranspose C.val) *
        J.form * (C.val * diagonal d) =
        diagonal (fun i => J.conj (d i)) * A * diagonal d := by
      simp only [A, mul_assoc]
    rw [he]
    ext i j
    simp only [diagonal_mul, mul_diagonal]
    by_cases hij : i = j
    · subst j
      rw [one_apply_eq]
      calc
        J.conj (d i) * A i i * d i = A i i * (d i * J.conj (d i)) := by ring
        _ = 1 := by rw [hd, mul_inv_cancel₀ (ha0 i)]
    · rw [hdiag hij, mul_zero, zero_mul, one_apply_ne hij]
  · intro a ha
    simpa only [mul_smul, hDC] using hframe a ha

end OrthogonalFrames

namespace OrthogonalFrames
variable {E : Type*} [Field E] [Finite E]

private theorem frame_gram_isDiag (J : HermitianForm 3 E) (p : ℕ)
    (hp : 1 < p) (hm : p % 3 = 2) (hE : Nat.card E = p ^ 2)
    (hc : ∀ x, J.conj x = x ^ p)
    (H : Subgroup J.specialSubgroup) (C : GL (Fin 3) E)
    (hframe : PreservesFrame H C)
    (hU : ∃ U : Subgroup J.specialSubgroup, U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    (J.conjTranspose C.val * J.form * C.val).IsDiag := by
  obtain ⟨U, hUH, hU, hn⟩ := hU
  let r : U →* GL (Fin 3) E :=
    { toFun := fun u => C⁻¹ * u.val.val * C
      map_one' := by simp
      map_mul' := fun u v => by simp [mul_assoc] }
  have hr : Function.Injective r := by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    change C⁻¹ * u.val.val * C = C⁻¹ * v.val.val * C at h
    exact mul_left_cancel (mul_right_cancel h)
  have hrm (u : U) : r u • HermitianForm.OddThreeLocal.Monomial.coordinateVectors (E := E) =
      HermitianForm.OddThreeLocal.Monomial.coordinateVectors := by
    change (C⁻¹ * u.val.val * C) • _ = _
    rw [mul_smul, mul_smul, hframe _ (hUH u.property), inv_smul_smul]
  let A : Matrix (Fin 3) (Fin 3) E := J.conjTranspose C.val * J.form * C.val
  have hrpres (u : U) : J.conjTranspose (r u).val * A * (r u).val = A := by
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
  intro i j hij
  obtain ⟨a, haD, hne⟩ := OrthogonalFrames.WeightAction.separating_diagonal r hrm hr hU hn i j hij
  obtain ⟨n, hn⟩ := hU a
  have hpow (k : Fin 3) : ((r a).val k k) ^ (3 ^ n) = 1 := by
    have he : (r a).val ^ (3 ^ n) = 1 := by
      have hh := congrArg (fun x : GL (Fin 3) E => x.val) (congrArg r hn)
      simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using hh
    rw [← haD.diagonal_diag, diagonal_pow] at he
    simpa only [diagonal_apply_eq, Pi.pow_apply, diag_apply, one_apply_eq] using
      congrArg (fun B : Matrix (Fin 3) (Fin 3) E => B k k) he
  have hnorm := norm_one J p hp hm hE hc ((r a).val i i) n (hpow i)
  have he := hrpres a
  rw [← haD.diagonal_diag, adjoint_diagonal] at he
  have heij := congrArg (fun B : Matrix (Fin 3) (Fin 3) E => B i j) he
  simp only [diagonal_mul, mul_diagonal, diag_apply] at heij
  change A i j = 0
  by_contra hz
  have hcoef : J.conj ((r a).val i i) * (r a).val j j = 1 := by
    apply mul_right_cancel₀ hz
    calc
      (J.conj ((r a).val i i) * (r a).val j j) * A i j =
          J.conj ((r a).val i i) * A i j * (r a).val j j := by ring
      _ = 1 * A i j := by simpa only [one_mul] using heij
  have hconj0 : J.conj ((r a).val i i) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hnorm
    exact zero_ne_one hnorm
  exact hne (mul_left_cancel₀ hconj0 (hnorm.trans hcoef.symm))

end OrthogonalFrames

/-- An invariant frame for a subgroup containing a nonabelian three-group can
be made orthonormal over the original quadratic field, without changing its lines. -/
public theorem orthogonalFrame_of_frame
    (p : ℕ) (hp : p.Prime) (_ho : Odd p) (_hgt : 3 < p) (hm : p % 3 = 2)
    (E : Type*) [Field E] [Finite E] (J : HermitianForm 3 E)
    (hE : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (H : Subgroup J.specialSubgroup)
    (hU : ∃ U : Subgroup J.specialSubgroup, U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U)
    (hf : HasFrame H) : HasOrthogonalFrame H := by
  obtain ⟨C, hC⟩ := hf
  exact OrthogonalFrames.normalize J p hp hE hc H C hC
    (OrthogonalFrames.frame_gram_isDiag J p hp.one_lt hm hE hc H C hC hU)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement
