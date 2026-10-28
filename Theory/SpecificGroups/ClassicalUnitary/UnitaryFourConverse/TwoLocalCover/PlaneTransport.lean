module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover.FixedRadical
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport

/-!
# Unitary transport of an isotropic plane in Hermitian four-space

Every totally isotropic plane is the image of the first coordinate plane under
an actual unitary matrix, over every field of order `(2 ^ n) ^ 2` with `n > 0`.
Choose a basis of the plane and dual partners using the dimension of its
Hermitian perpendicular. Trace surjectivity makes each partner isotropic;
adding a multiple of the first basis vector then kills the partners' mutual
pairing. Ordering these four vectors gives the antidiagonal Gram matrix, which
also proves that the resulting matrix is invertible.

This is the plane instance of GLS3 Lemma 2.7.1, printed p.89, used in the
parabolic geometry of chapter 3, printed pp.114–115
(`refs/KGroup/GLS3/chapter2.tex` and `chapter3.tex`). The frame construction
adapts `FiveIsotropicTransitivity/PlaneBasis/Frame.lean`, with isotropic rather
than norm-one partners. The field of order four is included. Special-unitary
transport is supplied separately by the determinant correction.
-/

noncomputable section

open Matrix Module BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover
variable {F : Type*} [Field F] (J : HermitianForm 4 F)

private lemma pairing_sum_left {ι : Type*} (s : Finset ι) (v : ι → Fin 4 → F)
    (w : Fin 4 → F) :
    pairing J (∑ i ∈ s, v i) w = ∑ i ∈ s, pairing J (v i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, pairing_add_left, ih]

private lemma exists_plane_dual_partners [Finite F] (W : Submodule F (Fin 4 → F))
    (hd : Module.finrank F W = 2) :
    ∃ (e : Basis (Fin 2) F W) (f : Fin 2 → Fin 4 → F),
      ∀ i j, pairing J (e i) (f j) = if i = j then 1 else 0 := by
  classical
  let e := Module.finBasisOfFinrankEq F W hd
  let T : (Fin 4 → F) →ₗ[F] (Fin 2 → F) := LinearMap.pi fun i => pairingMap J (e i)
  have hk : LinearMap.ker T = orthogonal J W := by
    ext v
    rw [LinearMap.mem_ker, funext_iff]
    change (∀ i, pairing J (e i) v = 0) ↔ ∀ w ∈ W, pairing J w v = 0
    constructor
    · intro hv w hw
      have he := congrArg (fun x : W => pairing J x.val v) (e.sum_repr ⟨w, hw⟩)
      rw [← he]
      simp only [Submodule.coe_sum, Submodule.coe_smul, pairing_sum_left, pairing_smul_left,
        hv, mul_zero, Finset.sum_const_zero]
    · intro hv i
      exact hv _ (e i).property
  have hr : LinearMap.range T = ⊤ := by
    apply Submodule.eq_top_iff_finrank_eq.mpr
    have hh := T.finrank_range_add_finrank_ker
    rw [hk, finrank_orthogonal, hd] at hh
    simp only [Module.finrank_pi, Fintype.card_fin] at hh ⊢
    omega
  have ht := LinearMap.range_eq_top.mp hr
  choose f hf using fun j : Fin 2 => ht (Pi.single j 1)
  refine ⟨e, f, ?_⟩
  intro i j
  have hh := congrFun (hf j) i
  simpa only [T, LinearMap.pi_apply, pairingMap, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.single_apply, eq_comm] using hh

private lemma pairing_reverse {v w : Fin 4 → F} {a : F} (h : pairing J v w = a) :
    pairing J w v = J.conj a := by rw [← pairing_conj, h]

private lemma exists_plane_frame [Finite F]
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (W : Submodule F (Fin 4 → F)) (hd : Module.finrank F W = 2)
    (hi : W ≤ orthogonal J W) :
    ∃ (e : Basis (Fin 2) F W) (v : Fin 4 → Fin 4 → F),
      v 0 = e 0 ∧ v 1 = e 1 ∧
        ∀ i j, pairing J (v i) (v j) = UnitaryFourFlag.gram F i j := by
  classical
  obtain ⟨e, f, hf⟩ := exists_plane_dual_partners J W hd
  have he (i j : Fin 2) : pairing J (e i) (e j) = 0 := hi (e j).property _ (e i).property
  have hfe (i j : Fin 2) : pairing J (f i) (e j) = if i = j then 1 else 0 := by
    rw [pairing_reverse J (hf j i)]
    split_ifs <;> simp_all
  have adjust (i : Fin 2) : ∃ g : Fin 4 → F,
      pairing J g g = 0 ∧ ∀ j, pairing J (e j) g = if j = i then 1 else 0 := by
    obtain ⟨a, ha⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective J (2 ^ n)
      hcard (UnitaryFourFormTransport.fixed_card J n hn hcard hconj)
      (-pairing J (f i) (f i)) (by rw [map_neg, pairing_conj])
    refine ⟨f i + a • (e i).val, ?_, ?_⟩
    · simp only [pairing_add_left, pairing_add_right, pairing_smul_left, pairing_smul_right,
        hf, hfe, he, ite_true, mul_one, mul_zero, add_zero]
      linear_combination ha
    · intro j
      simp only [pairing_add_right, pairing_smul_right, he, mul_zero, add_zero, hf]
  obtain ⟨u, huu, heu⟩ := adjust 0
  obtain ⟨w, hww, hew⟩ := adjust 1
  have hue (j : Fin 2) : pairing J u (e j) = if j = 0 then 1 else 0 := by
    rw [pairing_reverse J (heu j)]
    split_ifs <;> simp
  have hwe (j : Fin 2) : pairing J w (e j) = if j = 1 then 1 else 0 := by
    rw [pairing_reverse J (hew j)]
    split_ifs <;> simp
  let z := w + (-pairing J u w) • (e 0).val
  have huz : pairing J u z = 0 := by
    simp only [z, pairing_add_right, pairing_smul_right, hue, ite_true, mul_one,
      add_neg_cancel]
  have hez (j : Fin 2) : pairing J (e j) z = if j = 1 then 1 else 0 := by
    simp only [z, pairing_add_right, pairing_smul_right, he, hew, mul_zero, add_zero]
  have hzz : pairing J z z = 0 := by
    simp only [z, pairing_add_left, pairing_add_right, pairing_smul_left, pairing_smul_right,
      hwe, hew, he, hww]
    norm_num
  have hzu : pairing J z u = 0 := by simpa using pairing_reverse J huz
  have hze (j : Fin 2) : pairing J z (e j) = if j = 1 then 1 else 0 := by
    rw [pairing_reverse J (hez j)]
    split_ifs <;> simp
  refine ⟨e, ![(e 0).val, (e 1).val, z, u], rfl, rfl, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [UnitaryFourFlag.gram, he, heu, hue, hez, hze, huu, hzz, huz, hzu]

private def planeFrameMatrix (v : Fin 4 → Fin 4 → F) : Matrix (Fin 4) (Fin 4) F :=
  fun i j => v j i

private lemma planeFrameMatrix_mulVec (v : Fin 4 → Fin 4 → F) (x : Fin 4 → F) :
    planeFrameMatrix v *ᵥ x = x 0 • v 0 + x 1 • v 1 + x 2 • v 2 + x 3 • v 3 := by
  ext i
  simp [planeFrameMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    smul_eq_mul, mul_comm, add_assoc]

private lemma planeFrameMatrix_gram (v : Fin 4 → Fin 4 → F)
    (hv : ∀ i j, pairing J (v i) (v j) = UnitaryFourFlag.gram F i j) :
    J.conjTranspose (planeFrameMatrix v) * J.form * planeFrameMatrix v =
      UnitaryFourFlag.gram F := by
  rw [mul_assoc]
  ext i j
  exact hv i j

private lemma planeFrameMatrix_isUnit (v : Fin 4 → Fin 4 → F)
    (hv : ∀ i j, pairing J (v i) (v j) = UnitaryFourFlag.gram F i j) :
    IsUnit (planeFrameMatrix v) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h
  have hh := congrArg Matrix.det (planeFrameMatrix_gram J v hv)
  rw [Matrix.det_mul, h, mul_zero] at hh
  exact UnitaryFourFlag.gram_det_ne_zero F hh.symm

omit J in
/-- The plane case of Hermitian Witt extension, including the field of order four. -/
public theorem exists_plane_unitary_transport [Finite F] [CharP F 2]
    (σ : F ≃+* F) (hσ : Function.Involutive σ)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, σ x = x ^ (2 ^ n))
    (W : Submodule F (Fin 4 → F)) (hd : Module.finrank F W = 2)
    (hi : W ≤ orthogonal (UnitaryFourFlag.form F σ hσ) W) :
    ∃ A : GL (Fin 4) F, A ∈ (UnitaryFourFlag.form F σ hσ).unitarySubgroup ∧
      W = (UnitaryFourFlag.planeSpace F).map A.val.mulVecLin := by
  classical
  let J := UnitaryFourFlag.form F σ hσ
  obtain ⟨e, v, hv0, hv1, hv⟩ := exists_plane_frame J n hn hcard hconj W hd hi
  obtain ⟨A, hA⟩ := planeFrameMatrix_isUnit J v hv
  refine ⟨A, ?_, ?_⟩
  · apply (J.mem_unitarySubgroup_iff A).mpr
    rw [hA]
    exact planeFrameMatrix_gram J v hv
  · rw [hA]
    ext w
    constructor
    · intro hw
      let w' : W := ⟨w, hw⟩
      refine ⟨![e.repr w' 0, e.repr w' 1, 0, 0], ?_, ?_⟩
      · simp [UnitaryFourFlag.planeSpace]
      · change planeFrameMatrix v *ᵥ _ = w
        have he := congrArg Subtype.val (e.sum_repr w')
        simp [planeFrameMatrix_mulVec, hv0, hv1]
        simpa only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul] using he
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h2, h3⟩ := hx
      change planeFrameMatrix v *ᵥ x ∈ W
      rw [planeFrameMatrix_mulVec, h2, h3]
      simpa [hv0, hv1] using
        W.add_mem (W.smul_mem (x 0) (e 0).property) (W.smul_mem (x 1) (e 1).property)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover
