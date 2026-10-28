module

public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity.Coordinates
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicGeometry
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourFormTransport
public import BenderSuzuki.External.Huppert.II.theorem_10_4
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Tactic.FinCases

/-!
# Adapted Hermitian bases for isotropic lines in five-space

A nonzero isotropic vector is paired with a vector of norm one by solving
one trace equation over the field of sixteen elements. Their nondegenerate
plane has a three-dimensional perpendicular complement. Huppert II.10.4(a)
provides an orthonormal basis of that complement, giving an invertible matrix
with Gram matrix `referenceGram false` whose first column spans the given line.

This supplies the isotropic-line basis construction used in the Hermitian
case of Witt extension (GLS3, Lemma 2.7.1, printed p.89), as recorded in
`refs/KGroup/GLS3/chapter2.tex`. The special-unitary determinant correction
is separate from this basis-existence result.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive.IsotropicGeometry
namespace Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity
variable {F : Type*} [Field F]
local notation "V" => (Fin 5 → F)

private lemma p_add_l (J : HermitianForm 5 F) (x y z : V) :
    pairing J (x + y) z = pairing J x z + pairing J y z := by
  simp only [pairing, Pi.add_apply, map_add]
  change (∑ i, (J.conj (x i) + J.conj (y i)) * z i) = _
  rw [show (∑ i, (J.conj (x i) + J.conj (y i)) * z i) =
      ∑ i, (J.conj (x i) * z i + J.conj (y i) * z i) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [add_mul]]
  rw [Finset.sum_add_distrib]
  rfl

private lemma p_add_r (J : HermitianForm 5 F) (x y z : V) :
    pairing J x (y + z) = pairing J x y + pairing J x z := by
  simp only [pairing]
  rw [dotProduct_add]

private lemma p_smul_l (J : HermitianForm 5 F) (a : F) (x z : V) :
    pairing J (a • x) z = J.conj a * pairing J x z := by
  simp only [pairing]
  change (∑ i, J.conj (a * x i) * z i) = _
  simp only [map_mul]
  change (∑ i, J.conj a * J.conj (x i) * z i) =
    J.conj a * (∑ i, J.conj (x i) * z i)
  rw [show (∑ i, J.conj a * J.conj (x i) * z i) =
      ∑ i, J.conj a * (J.conj (x i) * z i) by
        apply Finset.sum_congr rfl
        intro i hi
        ring]
  rw [← Finset.mul_sum]

private lemma p_smul_r (J : HermitianForm 5 F) (a : F) (x z : V) :
    pairing J x (a • z) = a * pairing J x z := by
  simp only [pairing]
  rw [dotProduct_smul]
  rfl

private lemma p_symm (J : HermitianForm 5 F) (x y : V) :
    J.conj (pairing J x y) = pairing J y x := by
  change J.conj ((fun i => J.conj (x i)) ⬝ᵥ y) = _
  rw [show J.conj ((fun i => J.conj (x i)) ⬝ᵥ y) =
      ∑ i, J.conj (J.conj (x i) * y i) by simp [dotProduct, map_sum]]
  simp only [map_mul]
  change _ = ∑ i, J.conj (y i) * x i
  apply Finset.sum_congr rfl
  intro i hi
  rw [J.conj_involutive]
  ring

private def lineMap (J : HermitianForm 5 F) (v w : V) : V →ₗ[F] F × F where
  toFun x := (pairing J v x, pairing J w x)
  map_add' x y := by
    change (pairing J v (x + y), pairing J w (x + y)) =
      (pairing J v x + pairing J v y, pairing J w x + pairing J w y)
    rw [p_add_r, p_add_r]
  map_smul' a x := by
    change (pairing J v (a • x), pairing J w (a • x)) =
      (a * pairing J v x, a * pairing J w x)
    rw [p_smul_r, p_smul_r]

private def lineComplement (J : HermitianForm 5 F) (v w : V) : Submodule F V :=
  (lineMap J v w).ker

private lemma p_neg_r (J : HermitianForm 5 F) (x z : V) : pairing J x (-z) = -pairing J x z := by
  simpa using p_smul_r J (-1) x z

private lemma lineComplement_mem (J : HermitianForm 5 F) (v w x : V) :
    x ∈ lineComplement J v w ↔ pairing J v x = 0 ∧ pairing J w x = 0 := by
  rw [lineComplement, LinearMap.mem_ker]
  change ((pairing J v x, pairing J w x) = (0, 0)) ↔ _
  simp only [Prod.ext_iff]

private lemma complement_mem (J : HermitianForm 5 F) (v w : V) [CharP F 2]
    (hvv : pairing J v v = 0) (hvw : pairing J v w = 1)
    (hwv : pairing J w v = 1) (hww : pairing J w w = 1) (x : V) :
    x - (pairing J w x + pairing J v x) • v - pairing J v x • w ∈ lineComplement J v w := by
  rw [lineComplement_mem]
  simp only [sub_eq_add_neg]
  constructor
  · rw [p_add_r, p_add_r, p_neg_r, p_neg_r, p_smul_r, p_smul_r, hvw, hvv]
    ring_nf
  · rw [p_add_r, p_add_r, p_neg_r, p_neg_r, p_smul_r, p_smul_r, hwv, hww]
    ring_nf
    simp [CharTwo.two_eq_zero]

private lemma lineMap_surjective (J : HermitianForm 5 F) (v w : V) [CharP F 2]
    (hvv : pairing J v v = 0) (hvw : pairing J v w = 1)
    (hwv : pairing J w v = 1) (hww : pairing J w w = 1) :
    Function.Surjective (lineMap J v w) := by
  intro z
  refine ⟨(z.1 + z.2) • v + z.1 • w, ?_⟩
  change (pairing J v ((z.1 + z.2) • v + z.1 • w),
    pairing J w ((z.1 + z.2) • v + z.1 • w)) = z
  apply Prod.ext
  · change pairing J v ((z.1 + z.2) • v + z.1 • w) = z.1
    rw [p_add_r, p_smul_r, p_smul_r, hvv, hvw]
    ring
  · change pairing J w ((z.1 + z.2) • v + z.1 • w) = z.2
    rw [p_add_r, p_smul_r, p_smul_r, hwv, hww]
    ring_nf
    simp [CharTwo.two_eq_zero]

private lemma complement_finrank (J : HermitianForm 5 F) (v w : V) [CharP F 2]
    (hvv : pairing J v v = 0) (hvw : pairing J v w = 1)
    (hwv : pairing J w v = 1) (hww : pairing J w w = 1) :
    Module.finrank F (lineComplement J v w) = 3 := by
  have hs := lineMap_surjective J v w hvv hvw hwv hww
  have hr : (lineMap J v w).range = ⊤ := LinearMap.range_eq_top_of_surjective _ hs
  have hdim := LinearMap.finrank_range_add_finrank_ker (lineMap J v w)
  rw [hr] at hdim
  simp [finrank_top, Module.finrank_prod, Module.finrank_self] at hdim
  change Module.finrank F (lineMap J v w).ker = 3
  omega

private lemma exists_partner (J : HermitianForm 5 F) (v : V)
    (hvv : pairing J v v = 0) [CharP F 2] (hv : v ≠ 0) [Finite F]
    (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) :
    ∃ w : V, pairing J v w = 1 ∧ pairing J w v = 1 ∧ pairing J w w = 1 := by
  have hn : ¬ (∀ y : V, pairing J v y = 0) := by
    intro h
    have hz : (fun i => J.conj (v i)) = 0 := dotProduct_eq_zero _ (by
      intro y
      exact h y)
    apply hv
    funext i
    have hi := congrFun hz i
    have := congrArg J.conj hi
    simpa using this
  push Not at hn
  obtain ⟨y, hy⟩ := hn
  let y' := (pairing J v y)⁻¹ • y
  have hvy : pairing J v y' = 1 := by
    dsimp [y']
    rw [p_smul_r]
    exact inv_mul_cancel₀ hy
  have hyv : pairing J y' v = 1 := by
    have hh := p_symm J v y'
    rw [hvy] at hh
    simpa using hh.symm
  have hfix : J.conj (pairing J y' y') = pairing J y' y' := by
    rw [p_symm]
  have hcardfix := Theory.SpecificGroups.UnitaryFive.fixed_card_four J hcard hconj
  have hcard4 : Nat.card F = 4 ^ 2 := by simpa using hcard
  have hfix' : J.conj (1 + pairing J y' y') = 1 + pairing J y' y' := by
    rw [map_add, hfix]
    simp
  obtain ⟨c, hc⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective
    J 4 hcard4 hcardfix (1 + pairing J y' y') hfix'
  let w := y' + c • v
  refine ⟨w, ?_, ?_, ?_⟩
  · change pairing J v (y' + c • v) = 1
    rw [p_add_r, hvy, p_smul_r, hvv]
    simp
  · change pairing J (y' + c • v) v = 1
    rw [p_add_l, hyv, p_smul_l, hvv]
    simp
  · change pairing J (y' + c • v) (y' + c • v) = 1
    rw [p_add_l, p_add_r, p_add_r, p_smul_r J c y' v,
      p_smul_l J c v y', p_smul_l J c v (c • v), p_smul_r J c v v,
      hvy, hyv, hvv]
    simp only [mul_one, mul_zero, add_zero]
    rw [add_assoc, hc]
    ring_nf
    simp [CharTwo.two_eq_zero]

private lemma p_nondegenerate_right (J : HermitianForm 5 F) (x : V)
    (hx : ∀ y, pairing J y x = 0) : x = 0 := by
  ext i
  have h := hx (Pi.single i 1)
  simpa [pairing, dotProduct, Pi.single_apply] using h

private lemma complement_nondegenerate (J : HermitianForm 5 F) (v w : V) [CharP F 2]
    (hvv : pairing J v v = 0) (hvw : pairing J v w = 1)
    (hwv : pairing J w v = 1) (hww : pairing J w w = 1)
    (x : lineComplement J v w)
    (hx : ∀ y : lineComplement J v w, pairing J y.val x.val = 0) : x = 0 := by
  apply Subtype.ext
  apply p_nondegenerate_right J
  intro y
  have h := hx ⟨_, complement_mem J v w hvv hvw hwv hww y⟩
  have hxv := (lineComplement_mem J v w x.val).mp x.property
  change pairing J (y - (pairing J w y + pairing J v y) • v - pairing J v y • w) x.val = 0 at h
  have p_neg_l (a b : V) : pairing J (-a) b = -pairing J a b := by
    simpa using p_smul_l J (-1) a b
  simpa only [sub_eq_add_neg, p_add_l, p_neg_l, p_smul_l,
    hxv.1, hxv.2, mul_zero, neg_zero, add_zero] using h

private lemma pairing_mulVec_left {n : Type*} [Fintype n]
    (J : HermitianForm 5 F) (A : Matrix (Fin 5) n F) (x : n → F) (y : V) :
    pairing J (A *ᵥ x) y = (fun i => J.conj (x i)) ⬝ᵥ (A.map J.conj).transpose *ᵥ y := by
  unfold pairing
  rw [show (fun i => J.conj ((A *ᵥ x) i)) =
      (A.map J.conj) *ᵥ (fun i => J.conj (x i)) from
    funext (RingHom.map_mulVec J.conj.toRingHom A x)]
  rw [← vecMul_transpose, ← dotProduct_mulVec]

private lemma basisMatrix_mulVec (C : Submodule F V) (b : Module.Basis (Fin 3) F C)
    (a : Fin 3 → F) :
    (Matrix.of fun i j => (b j).val i : Matrix (Fin 5) (Fin 3) F) *ᵥ a =
      (b.equivFun.symm a).val := by
  rw [Module.Basis.equivFun_symm_apply]
  ext i
  simp [mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]

private lemma complement_gram_nondegenerate (J : HermitianForm 5 F) (v w : V) [CharP F 2]
    (hvv : pairing J v v = 0) (hvw : pairing J v w = 1)
    (hwv : pairing J w v = 1) (hww : pairing J w w = 1)
    (b : Module.Basis (Fin 3) F (lineComplement J v w)) :
    let U : Matrix (Fin 5) (Fin 3) F := Matrix.of fun i j => (b j).val i
    ((U.map J.conj).transpose * U).det ≠ 0 := by
  dsimp only
  let U : Matrix (Fin 5) (Fin 3) F := Matrix.of fun i j => (b j).val i
  intro hdet
  obtain ⟨a, ha, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h : b.equivFun.symm a = 0 := by
    apply complement_nondegenerate J v w hvv hvw hwv hww
    intro y
    obtain ⟨z, rfl⟩ := b.equivFun.symm.surjective y
    rw [← basisMatrix_mulVec, ← basisMatrix_mulVec, pairing_mulVec_left,
      mulVec_mulVec]
    change (fun i => J.conj (z i)) ⬝ᵥ ((U.map J.conj).transpose * U) *ᵥ a = 0
    rw [hzero, dotProduct_zero]
  apply ha
  exact b.equivFun.symm.injective (h.trans (map_zero _).symm)

private lemma exists_complement_orthonormal (J : HermitianForm 5 F) (v w : V)
    [Finite F] [CharP F 2] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (hvv : pairing J v v = 0) (hvw : pairing J v w = 1)
    (hwv : pairing J w v = 1) (hww : pairing J w w = 1) :
    ∃ c : Fin 3 → V, (∀ i, c i ∈ lineComplement J v w) ∧
      ∀ i j, pairing J (c i) (c j) = if i = j then 1 else 0 := by
  classical
  let C := lineComplement J v w
  let b := Module.finBasisOfFinrankEq F C (complement_finrank J v w hvv hvw hwv hww)
  let U : Matrix (Fin 5) (Fin 3) F := Matrix.of fun i j => (b j).val i
  let K : HermitianForm 3 F :=
    { conj := J.conj
      conj_involutive := J.conj_involutive
      form := (U.map J.conj).transpose * U
      form_hermitian := by
        intro i j
        change J.conj (pairing J (fun k => U k j) (fun k => U k i)) =
          pairing J (fun k => U k i) (fun k => U k j)
        exact p_symm J _ _
      form_nondegenerate := complement_gram_nondegenerate J v w hvv hvw hwv hww b }
  obtain ⟨D, hD⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    3 K 4 hcard (fixed_card_four J hcard hconj)
  let Q : Matrix (Fin 5) (Fin 3) F := U * D.val
  have hQ : (Q.map J.conj).transpose * Q = 1 := by
    change ((U * D.val).map J.conj).transpose * (U * D.val) = 1
    rw [Matrix.map_mul, transpose_mul]
    change (D.val.map J.conj).transpose * ((U.map J.conj).transpose * U) * D.val = 1 at hD
    simpa only [Matrix.mul_assoc] using hD
  refine ⟨fun i k => Q k i, ?_, ?_⟩
  · intro i
    have h := basisMatrix_mulVec C b (fun j => D.val j i)
    change (fun k => (U *ᵥ (fun j => D.val j i)) k) ∈ C
    rw [h]
    exact (b.equivFun.symm _).property
  · intro i j
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A i j) hQ
    exact h

private lemma referenceGram_line_nondegenerate :
    (referenceGram false : Matrix (Fin 5) (Fin 5) F).det ≠ 0 := by
  intro h
  obtain ⟨x, hx, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  apply hx
  have hh := congrFun hz
  have h1 := hh 0
  have h0 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  have h4 := hh 4
  simp [referenceGram, mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h3 h4
  ext i
  fin_cases i <;> simp_all

private lemma gram_from_columns (J : HermitianForm 5 F) (v w : V) (c : Fin 3 → V)
    (hvv : pairing J v v = 0) (hvw : pairing J v w = 1)
    (hwv : pairing J w v = 1) (hww : pairing J w w = 1)
    (hc : ∀ i, c i ∈ lineComplement J v w)
    (hcc : ∀ i j, pairing J (c i) (c j) = if i = j then 1 else 0) :
    let P : Matrix (Fin 5) (Fin 5) F := Matrix.of fun i j => (![v, w, c 0, c 1, c 2] j) i
    J.conjTranspose P * P = referenceGram false := by
  let P : Matrix (Fin 5) (Fin 5) F := Matrix.of fun i j => (![v, w, c 0, c 1, c 2] j) i
  have hvc (i) : pairing J v (c i) = 0 := ((lineComplement_mem J v w _).mp (hc i)).1
  have hwc (i) : pairing J w (c i) = 0 := ((lineComplement_mem J v w _).mp (hc i)).2
  have hcv (i) : pairing J (c i) v = 0 := by rw [← p_symm, hvc, map_zero]
  have hcw (i) : pairing J (c i) w = 0 := by rw [← p_symm, hwc, map_zero]
  change J.conjTranspose P * P = referenceGram false
  ext i j
  change pairing J (![v, w, c 0, c 1, c 2] i) (![v, w, c 0, c 1, c 2] j) = _
  fin_cases i <;> fin_cases j <;>
    simp [referenceGram, hvv, hvw, hwv, hww, hvc, hwc, hcv, hcw, hcc]

/-- Every isotropic line admits the prescribed Hermitian adapted basis. -/
theorem hasAdaptedBasis_line (J : HermitianForm 5 F) [Finite F] [CharP F 2]
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (_hJ : J.form = 1) (W : Submodule F V)
    (hd : Module.finrank F W = 1) (hi : W ≤ orthogonal J W) :
    HasAdaptedBasis J false W := by
  classical
  have hW : W ≠ ⊥ := by
    intro h
    rw [h] at hd
    simp at hd
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hvv : pairing J v v = 0 := hi hvW v hvW
  obtain ⟨w, hvw, hwv, hww⟩ := exists_partner J v hvv hv0 hcard hconj
  obtain ⟨c, hc, hcc⟩ := exists_complement_orthonormal J v w hcard hconj hvv hvw hwv hww
  let P : Matrix (Fin 5) (Fin 5) F := Matrix.of fun i j => (![v, w, c 0, c 1, c 2] j) i
  have hP : J.conjTranspose P * P = referenceGram false :=
    gram_from_columns J v w c hvv hvw hwv hww hc hcc
  have hdet : P.det ≠ 0 := by
    intro h
    have he := congrArg Matrix.det hP
    rw [det_mul, h, mul_zero] at he
    exact referenceGram_line_nondegenerate he.symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hdet, hP, ?_⟩
  change W = (coordinateSubspace F false).map P.mulVecLin
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hd hvW hv0]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    obtain rfl : x = v := Set.mem_singleton_iff.mp hx
    refine ⟨Pi.single 0 1, ?_, ?_⟩
    · change (Pi.single (0 : Fin 5) (1 : F)) 1 = 0 ∧
        (Pi.single (0 : Fin 5) (1 : F)) 3 = 0 ∧
        (Pi.single (0 : Fin 5) (1 : F)) 4 = 0 ∧
        (false = false → (Pi.single (0 : Fin 5) (1 : F)) 2 = 0)
      simp
    · ext i
      simp [P, mulVec, dotProduct, Pi.single_apply]
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y 1 = 0 ∧ y 3 = 0 ∧ y 4 = 0 ∧ y 2 = 0 := by
      simpa [coordinateSubspace] using hy
    have he : P *ᵥ y = y 0 • v := by
      ext i
      simp [P, mulVec, dotProduct, Fin.sum_univ_succ,
        hy'.1, hy'.2.1, hy'.2.2.1, hy'.2.2.2, mul_comm]
    change P *ᵥ y ∈ Submodule.span F {v}
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

end Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity
