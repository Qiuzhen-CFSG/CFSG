module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.Basic
public import BenderSuzuki.External.Huppert.II.theorem_10_4
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# The canonical frame of common eigenlines

A common eigenbasis of a special unitary subgroup with no isotropic fixed
line has three distinct weights. Indeed, a scalar plane would contain two
orthogonal anisotropic common eigenvectors; norm surjectivity then produces
an isotropic common eigenvector, contradicting the no-Borel hypothesis.
Preservation of the Hermitian pairing makes distinct weights orthogonal.

The coordinate equations show that every common eigenline is one of the
three basis lines. Scaling by norms over the original field produces an
orthonormal frame with exactly this entire common-eigenline set. Its setwise
stabilizer therefore contains the subgroup and every normalizing element,
and lies in the normalizer of the literal special frame torus.

This proves the canonical-frame construction used in GLS4, Chapter 4,
Lemma 3.11(a), `refs/KGroup/GLS4/Chapter4.tex`, lines 585–603. Existence of
the supplied eigenbasis is a separate spectral descent step. The norm
surjectivity input is Huppert II.10.4 over the two stated finite-field
cardinalities; it is proved here as an input consequence, not assumed.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise LinearAlgebra.Projectivization
namespace UnitaryThree.OddTorusNormalizer.AbelianFrame
variable {E : Type*} [Field E]

private def pairing (J : HermitianForm 3 E) (v w : Fin 3 → E) : E :=
  dotProduct (fun i => J.conj (v i)) (J.form.mulVec w)

private lemma pairing_add_left (J : HermitianForm 3 E) (u v w : Fin 3 → E) :
    pairing J (u + v) w = pairing J u w + pairing J v w := by
  simp [pairing, Pi.add_apply, map_add, dotProduct, add_mul, Finset.sum_add_distrib]

private lemma pairing_add_right (J : HermitianForm 3 E) (u v w : Fin 3 → E) :
    pairing J u (v + w) = pairing J u v + pairing J u w := by
  simp [pairing, Matrix.mulVec_add, dotProduct_add]

private lemma pairing_smul_left (J : HermitianForm 3 E) (c : E) (v w : Fin 3 → E) :
    pairing J (c • v) w = J.conj c * pairing J v w := by
  simp [pairing, Pi.smul_apply, smul_eq_mul, map_mul, dotProduct, Finset.mul_sum,
    mul_assoc]

private lemma pairing_smul_right (J : HermitianForm 3 E) (c : E) (v w : Fin 3 → E) :
    pairing J v (c • w) = c * pairing J v w := by
  simp [pairing, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma pairing_conj (J : HermitianForm 3 E) (v w : Fin 3 → E) :
    J.conj (pairing J v w) = pairing J w v := by
  simp only [pairing, dotProduct, Matrix.mulVec, map_sum, map_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [J.form_hermitian, J.conj_involutive]
  ring

private lemma pairing_invariant (J : HermitianForm 3 E) (x : J.specialSubgroup)
    (v w : Fin 3 → E) : pairing J (x • v) (x • w) = pairing J v w := by
  let : Star E := ⟨J.conj⟩
  let : InvolutiveStar E := ⟨J.conj_involutive⟩
  let : StarMul E := ⟨fun r s => by
    change J.conj (r * s) = J.conj s * J.conj r
    rw [map_mul, mul_comm]⟩
  let : StarRing E := ⟨fun r s => by
    change J.conj (r + s) = J.conj r + J.conj s
    rw [map_add]⟩
  let A := x.val.val
  change star (A *ᵥ v) ⬝ᵥ J.form *ᵥ (A *ᵥ w) = star v ⬝ᵥ J.form *ᵥ w
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  change star v ᵥ* (J.conjTranspose A * J.form * A) ⬝ᵥ w = _
  rw [(J.mem_specialSubgroup_iff x.val).mp x.property |>.1]
  exact (Matrix.dotProduct_mulVec _ _ _).symm

private lemma commonEigenline_iff (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) (v : Fin 3 → E) (hv : v ≠ 0) :
    Projectivization.mk E v hv ∈ commonEigenlines J H ↔
      ∀ x ∈ H, ∃ c : E, x • v = c • v := by
  constructor
  · intro h x hx
    have hh : x.val • Projectivization.mk E v hv = Projectivization.mk E v hv := h hx
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at hh
    exact hh.imp fun c hc => hc.symm
  · intro h x hx
    change x.val • Projectivization.mk E v hv = Projectivization.mk E v hv
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    exact (h x hx).imp fun c hc => hc.symm

private lemma eigenvector_anisotropic (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) (hB : SpecialNoBorel J H)
    (v : Fin 3 → E) (hv : v ≠ 0)
    (h : ∀ x ∈ H, ∃ c : E, x • v = c • v) : pairing J v v ≠ 0 := by
  intro hz
  exact commonEigenline_not_isotropic J H hB ((commonEigenline_iff J H v hv).mpr h)
    ⟨v, hv, rfl, hz⟩

private lemma no_scalar_plane [Finite E] (J : HermitianForm 3 E)
    (q : ℕ) (hE : Nat.card E = q ^ 2)
    (hfix : Nat.card {x : E // J.conj x = x} = q)
    (H : Subgroup J.specialSubgroup) (hB : SpecialNoBorel J H)
    (b : Module.Basis (Fin 3) E (Fin 3 → E)) (i j : Fin 3) (hij : i ≠ j)
    (a : H → E) (hi : ∀ x : H, (x : J.specialSubgroup) • b i = a x • b i)
    (hj : ∀ x : H, (x : J.specialSubgroup) • b j = a x • b j) : False := by
  classical
  have hui : pairing J (b i) (b i) ≠ 0 :=
    eigenvector_anisotropic J H hB (b i) (b.ne_zero i)
      (fun x hx => ⟨a ⟨x, hx⟩, hi ⟨x, hx⟩⟩)
  let c := -pairing J (b i) (b j) / pairing J (b i) (b i)
  let w := b j + c • b i
  have hwj : b.repr w j = 1 := by simp [w, hij.symm]
  have hw : w ≠ 0 := by
    intro h
    simp [h] at hwj
  have hwe (x : H) : (x : J.specialSubgroup) • w = a x • w := by
    dsimp only [w]
    rw [smul_add, smul_comm (x : J.specialSubgroup) c, hi, hj]
    module
  have hww : pairing J w w ≠ 0 :=
    eigenvector_anisotropic J H hB w hw (fun x hx => ⟨a ⟨x, hx⟩, hwe ⟨x, hx⟩⟩)
  have hiw : pairing J (b i) w = 0 := by
    rw [pairing_add_right, pairing_smul_right]
    dsimp only [c]
    rw [div_mul_cancel₀ _ hui, add_neg_cancel]
  have hwi : pairing J w (b i) = 0 := by
    rw [← pairing_conj, hiw, map_zero]
  obtain ⟨d, hd, hdn⟩ := BenderSuzuki.External.huppert_II_10_4_norm_surjective
    J q hE hfix (-pairing J (b i) (b i) / pairing J w w)
    (by rw [map_div₀, map_neg, pairing_conj, pairing_conj])
    (div_ne_zero (neg_ne_zero.mpr hui) hww)
  let z := b i + d • w
  have hzj : b.repr z j = d := by simp [z, hwj, hij]
  have hz : z ≠ 0 := by
    intro h
    apply hd
    simpa [h] using hzj.symm
  have hze (x : H) : (x : J.specialSubgroup) • z = a x • z := by
    dsimp only [z]
    rw [smul_add, smul_comm (x : J.specialSubgroup) d, hi, hwe]
    module
  apply eigenvector_anisotropic J H hB z hz (fun x hx => ⟨a ⟨x, hx⟩, hze ⟨x, hx⟩⟩)
  dsimp only [z]
  rw [pairing_add_left, pairing_add_right, pairing_add_right,
    pairing_smul_left, pairing_smul_right, pairing_smul_left,
    pairing_smul_right, hiw, hwi]
  calc
    pairing J (b i) (b i) + d * 0 +
        (J.conj d * 0 + J.conj d * (d * pairing J w w)) =
        pairing J (b i) (b i) + (d * J.conj d) * pairing J w w := by ring
    _ = 0 := by rw [hdn, div_mul_cancel₀ _ hww, add_neg_cancel]

private lemma eigenbasis_weights_separate [Finite E] (J : HermitianForm 3 E)
    (q : ℕ) (hE : Nat.card E = q ^ 2)
    (hfix : Nat.card {x : E // J.conj x = x} = q)
    (H : Subgroup J.specialSubgroup) (hB : SpecialNoBorel J H)
    (b : Module.Basis (Fin 3) E (Fin 3 → E))
    (a : H → Fin 3 → E)
    (ha : ∀ (x : H) i, (x : J.specialSubgroup) • b i = a x i • b i)
    (i j : Fin 3) (hij : i ≠ j) : ∃ x : H, a x i ≠ a x j := by
  by_contra! h
  exact no_scalar_plane J q hE hfix H hB b i j hij (fun x => a x i)
    (fun x => ha x i) (fun x => by rw [ha, h])

private lemma eigenbasis_orthogonal (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) (hB : SpecialNoBorel J H)
    (b : Module.Basis (Fin 3) E (Fin 3 → E))
    (a : H → Fin 3 → E)
    (ha : ∀ (x : H) i, (x : J.specialSubgroup) • b i = a x i • b i)
    (hsep : ∀ i j, i ≠ j → ∃ x : H, a x i ≠ a x j) :
    ∀ i j, i ≠ j → pairing J (b i) (b j) = 0 := by
  intro i j hij
  obtain ⟨x, hx⟩ := hsep i j hij
  have hui : pairing J (b i) (b i) ≠ 0 :=
    eigenvector_anisotropic J H hB (b i) (b.ne_zero i)
      (fun x hx => ⟨a ⟨x, hx⟩ i, ha ⟨x, hx⟩ i⟩)
  have hi := pairing_invariant J (x : J.specialSubgroup) (b i) (b i)
  rw [ha, pairing_smul_left, pairing_smul_right] at hi
  have hn : J.conj (a x i) * a x i = 1 := by
    apply mul_right_cancel₀ hui
    simpa only [mul_assoc, one_mul] using hi
  by_contra hnz
  have hij' := pairing_invariant J (x : J.specialSubgroup) (b i) (b j)
  rw [ha, ha, pairing_smul_left, pairing_smul_right] at hij'
  have hrel : J.conj (a x i) * a x j = 1 := by
    apply mul_right_cancel₀ hnz
    simpa only [mul_assoc, one_mul] using hij'
  exact hx (mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hn) (hn.trans hrel.symm))

private lemma eigenbasis_coordinates (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup)
    (b : Module.Basis (Fin 3) E (Fin 3 → E))
    (a : H → Fin 3 → E)
    (ha : ∀ (x : H) i, (x : J.specialSubgroup) • b i = a x i • b i)
    (x : H) (v : Fin 3 → E) (i : Fin 3) :
    b.repr ((x : J.specialSubgroup) • v) i = a x i * b.repr v i := by
  have he : (x : J.specialSubgroup) • v =
      ∑ j, b.repr v j • (a x j • b j) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_comm, ha]
  rw [he]
  simp [smul_smul, Finsupp.single_apply, mul_comm]

private lemma commonEigenlines_eq_basisLines (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup)
    (b : Module.Basis (Fin 3) E (Fin 3 → E)) (hb : IsCommonEigenbasis J H b)
    (a : H → Fin 3 → E)
    (ha : ∀ (x : H) i, (x : J.specialSubgroup) • b i = a x i • b i)
    (hsep : ∀ i j, i ≠ j → ∃ x : H, a x i ≠ a x j) :
    commonEigenlines J H =
      Set.range (fun i => Projectivization.mk E (b i) (b.ne_zero i)) := by
  classical
  apply Set.Subset.antisymm
  · intro l hl
    induction l using Projectivization.ind with
    | _ v hv =>
      have he := (commonEigenline_iff J H v hv).mp hl
      have hex : ∃ i, b.repr v i ≠ 0 := by
        by_contra! h
        apply hv
        apply b.repr.injective
        ext i
        simp [h]
      obtain ⟨i, hi⟩ := hex
      have hcoord (x : H) (c : E) (hc : (x : J.specialSubgroup) • v = c • v)
          (j : Fin 3) (hj : b.repr v j ≠ 0) : a x j = c := by
        apply mul_right_cancel₀ hj
        have h := eigenbasis_coordinates J H b a ha x v j
        rw [hc] at h
        simpa using h.symm
      have hzero (j : Fin 3) (hji : j ≠ i) : b.repr v j = 0 := by
        by_contra hj
        obtain ⟨x, hx⟩ := hsep i j hji.symm
        obtain ⟨c, hc⟩ := he x x.property
        exact hx ((hcoord x c hc i hi).trans (hcoord x c hc j hj).symm)
      have hvb : v = b.repr v i • b i := by
        nth_rw 1 [← b.sum_repr v]
        apply Finset.sum_eq_single i
        · intro j _ hji
          rw [hzero j hji, zero_smul]
        · simp
      refine ⟨i, ?_⟩
      symm
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨b.repr v i, hvb.symm⟩
  · rintro l ⟨i, rfl⟩
    exact hb i

private lemma gram_entry (J : HermitianForm 3 E) (M : Matrix (Fin 3) (Fin 3) E)
    (i j : Fin 3) :
    (J.conjTranspose M * J.form * M) i j =
      pairing J (fun k => M k i) (fun k => M k j) := by
  simp only [HermitianForm.conjTranspose, Matrix.mul_apply, pairing,
    dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

private lemma exists_frame_eq_basisLines [Finite E] (J : HermitianForm 3 E)
    (q : ℕ) (hE : Nat.card E = q ^ 2)
    (hfix : Nat.card {x : E // J.conj x = x} = q)
    (b : Module.Basis (Fin 3) E (Fin 3 → E))
    (hoff : ∀ i j, i ≠ j → pairing J (b i) (b j) = 0)
    (hdiag : ∀ i, pairing J (b i) (b i) ≠ 0) :
    ∃ P : OrthogonalFrame J,
      Set.range (fun i => Projectivization.mk E (b i) (b.ne_zero i)) = frameLines P := by
  classical
  have hscale (i : Fin 3) : ∃ d : E, d ≠ 0 ∧
      d * J.conj d = (pairing J (b i) (b i))⁻¹ :=
    BenderSuzuki.External.huppert_II_10_4_norm_surjective J q hE hfix _
      (by rw [map_inv₀, pairing_conj]) (inv_ne_zero (hdiag i))
  choose d hd hdn using hscale
  let c := b.unitsSMul (fun i => Units.mk0 (d i) (hd i))
  have hc (i : Fin 3) : c i = d i • b i := by
    simp [c, Module.Basis.unitsSMul_apply, Units.smul_def]
  have horth (i j : Fin 3) : pairing J (c i) (c j) = if i = j then 1 else 0 := by
    rw [hc, hc, pairing_smul_left, pairing_smul_right]
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      calc
        J.conj (d i) * (d i * pairing J (b i) (b i)) =
            (d i * J.conj (d i)) * pairing J (b i) (b i) := by ring
        _ = 1 := by rw [hdn, inv_mul_cancel₀ (hdiag i)]
    · rw [if_neg hij, hoff i j hij, mul_zero, mul_zero]
  let e := Pi.basisFun E (Fin 3)
  let M := e.toMatrix c
  have hMdet : M.det ≠ 0 := by
    apply IsUnit.ne_zero
    rw [← e.det_apply]
    exact e.isUnit_det c
  let P : GL (Fin 3) E := Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet
  have hcol (i : Fin 3) : (fun k => M k i) = c i := by
    ext k
    simp [M, e, Module.Basis.toMatrix_apply]
  have hP : J.conjTranspose P.val * J.form * P.val = 1 := by
    ext i j
    change (J.conjTranspose M * J.form * M) i j = _
    rw [gram_entry, hcol, hcol, horth]
    rfl
  refine ⟨⟨P, hP⟩, ?_⟩
  have hline (i : Fin 3) : P • coordinateLine i =
      Projectivization.mk E (b i) (b.ne_zero i) := by
    rw [coordinateLine, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 (d i) (hd i), ?_⟩
    change d i • b i = M *ᵥ Pi.single i 1
    rw [Matrix.mulVec_single_one]
    change d i • b i = (fun k => M k i)
    rw [hcol, hc]
  change _ = P • Set.range (coordinateLine (E := E))
  ext l
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨coordinateLine i, ⟨i, rfl⟩, hline i⟩
  · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (hline i).symm⟩

/-- A common eigenbasis and no isotropic fixed line determine the entire
common-eigenline set as the three lines of an orthonormal frame over `E`. -/
public theorem exists_frame_eq_commonEigenlines [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (_hn : 2 ≤ n) (hE : Nat.card E = (2 ^ n) ^ 2)
    (hfix : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hB : SpecialNoBorel J H)
    (b : Module.Basis (Fin 3) E (Fin 3 → E)) (hb : IsCommonEigenbasis J H b) :
    ∃ P : OrthogonalFrame J, commonEigenlines J H = frameLines P := by
  classical
  have he (x : H) (i : Fin 3) :
      ∃ c : E, (x : J.specialSubgroup) • b i = c • b i :=
    (commonEigenline_iff J H (b i) (b.ne_zero i)).mp (hb i) x x.property
  choose a ha using he
  have hsep := eigenbasis_weights_separate J (2 ^ n) hE hfix H hB b a ha
  have hoff := eigenbasis_orthogonal J H hB b a ha hsep
  have hdiag (i : Fin 3) : pairing J (b i) (b i) ≠ 0 :=
    eigenvector_anisotropic J H hB (b i) (b.ne_zero i)
      (fun x hx => ⟨a ⟨x, hx⟩ i, ha ⟨x, hx⟩ i⟩)
  obtain ⟨P, hP⟩ := exists_frame_eq_basisLines J (2 ^ n) hE hfix b hoff hdiag
  exact ⟨P, (commonEigenlines_eq_basisLines J H b hb a ha hsep).trans hP⟩

/-- The frame constructed from the common eigenbasis simultaneously places
`H` and any normalizing element in its stabilizer and literal torus normalizer.
This is the canonical-frame step of GLS4, Chapter 4, Lemma 3.11(a); spectral
existence of the supplied basis remains the responsibility of its caller. -/
public theorem special_frame_and_placement_of_commonEigenbasis [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2 ^ n) ^ 2)
    (hfix : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hB : SpecialNoBorel J H)
    (b : Module.Basis (Fin 3) E (Fin 3 → E)) (hb : IsCommonEigenbasis J H b)
    (t : J.specialSubgroup) (htH : t ∈ normalizer H) :
    ∃ P : OrthogonalFrame J, commonEigenlines J H = frameLines P ∧
      H ⊔ zpowers t ≤ specialFrameStabilizer J P ∧
      H ⊔ zpowers t ≤ normalizer (specialFrameTorus J P) := by
  obtain ⟨P, hP⟩ := exists_frame_eq_commonEigenlines J hn hE hfix H hB b hb
  exact ⟨P, hP, special_frame_of_commonEigenlines J H t htH P hP,
    special_placement_of_commonEigenlines J H t htH P hP⟩

end UnitaryThree.OddTorusNormalizer.AbelianFrame
