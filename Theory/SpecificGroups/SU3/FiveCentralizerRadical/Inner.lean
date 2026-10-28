module

public import Theory.SpecificGroups.SU3.InvolutionConjugacy
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.ScalarKernel
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.SolvableResidual
public import ABG.ChapterII.Section2.SpecialUnitaryEquivSL2
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Centralizing the involution-centralizer residual in PSU₃(5)

The actual determinant-one SU₂ block is perfect, by its equivalence with
SL₂(5), so its projective image lies in the solvable residual of the full
involution centralizer. Perfectness lifts commutation with this image through
the central scalar kernel of SU₃ → PSU₃. The block contains the standard
involution, forcing a commuting matrix into the GU₂ block centralizer.
Noncommutativity of SU₂ then makes that two-dimensional block scalar.

The remaining matrix is `diag(a,a,a⁻²)`. Unitarity gives `a⁶ = 1`, and
multiplication by the scalar `a²` yields `diag(a³,a³,1)`, either the identity
or the standard involution. Involution lifting, conjugacy, and genuine
projective form equivalences extend the result to every nondegenerate
Hermitian form over a field of order 25 with conjugation `x ↦ x⁵`.

Source: Aschbacher--Smith, A.3.21(a), printed p.55, and E.1.14(7),
printed p.214, citing Aschbacher (1982), Lemma 4.11.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped Matrix
namespace Matrix.SU3.FiveCentralizerRadical
variable {F : Type*} [Field F]

private noncomputable def specialBlock (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj) :
    J2.specialSubgroup →* J3.specialSubgroup :=
  (blockEmbedding J3 J2 h3 h2 hc).comp
    (Subgroup.inclusion J2.specialSubgroup_le_unitarySubgroup)

private def negativeTwo (J : HermitianForm 2 F) (hJ : J.form = 1) :
    J.specialSubgroup :=
  ⟨GeneralLinearGroup.scalar (Fin 2) (-1), by
    rw [J.mem_specialSubgroup_iff, hJ]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two,
          GeneralLinearGroup.scalar]
    · simp [GeneralLinearGroup.det_scalar]⟩

private lemma specialBlock_negativeTwo (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj) :
    specialBlock J3 J2 h3 h2 hc (negativeTwo J2 h2) = standardInvolution J3 h3 := by
  apply Subtype.ext
  apply Units.ext
  change SL3.blockMatrix F (GeneralLinearGroup.scalar (Fin 2) (-1)) = _
  rw [standardInvolution_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SL3.blockMatrix, GeneralLinearGroup.scalar, Matrix.det_fin_two]

private lemma scalar_block_projective (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj)
    (hc5 : ∀ x, J2.conj x = x ^ 5) (A : J2.unitarySubgroup)
    (u : Fˣ) (hu : GeneralLinearGroup.scalar (Fin 2) u = A.val) :
    J3.specialToProjective (blockEmbedding J3 J2 h3 h2 hc A) ∈
      zpowers (J3.specialToProjective (standardInvolution J3 h3)) := by
  have hnorm : (u : F) ^ 5 * (u : F) = 1 := by
    have h := A.property
    rw [J2.mem_unitarySubgroup_iff, h2, mul_one, ← hu] at h
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h
    simpa [HermitianForm.conjTranspose, GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two, hc5] using he
  have h6 : (u : F) ^ 6 = 1 := by simpa only [pow_succ] using hnorm
  have h3sq : ((u : F) ^ 3) ^ 2 = 1 := by simpa only [← pow_mul] using h6
  have hmat : (blockEmbedding J3 J2 h3 h2 hc A).val.val =
      !![(u : F), 0, 0; 0, (u : F), 0; 0, 0, (u : F)⁻¹ ^ 2] := by
    rw [blockEmbedding_val, ← hu]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SL3.blockMatrix, GeneralLinearGroup.scalar]
  have hcancel : (u : F) * (u : F) ^ 2 = (u : F) ^ 3 := by ring
  rcases sq_eq_one_iff.mp h3sq with hone | hneg
  · have he : J3.specialToProjective (blockEmbedding J3 J2 h3 h2 hc A) = 1 := by
      apply Subtype.ext
      rw [J3.specialToProjective_apply_val]
      change ProjGenLinGroup.mk (blockEmbedding J3 J2 h3 h2 hc A).val =
        ProjGenLinGroup.mk (1 : GL (Fin 3) F)
      apply ProjGenLinGroup.mk_eq_mk_iff.mpr
      refine ⟨u ^ 2, ?_⟩
      apply Units.ext
      change (blockEmbedding J3 J2 h3 h2 hc A).val.val *
        (GeneralLinearGroup.scalar (Fin 3) (u ^ 2)).val = 1
      rw [hmat, GeneralLinearGroup.coe_scalar]
      simp only [Units.val_pow_eq_pow_val, Matrix.scalar_apply]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, hcancel, hone]
    rw [he]
    exact one_mem _
  · have he : J3.specialToProjective (blockEmbedding J3 J2 h3 h2 hc A) =
        J3.specialToProjective (standardInvolution J3 h3) := by
      apply Subtype.ext
      simp only [J3.specialToProjective_apply_val]
      apply ProjGenLinGroup.mk_eq_mk_iff.mpr
      refine ⟨u ^ 2, ?_⟩
      apply Units.ext
      change (blockEmbedding J3 J2 h3 h2 hc A).val.val *
        (GeneralLinearGroup.scalar (Fin 3) (u ^ 2)).val =
          (standardInvolution J3 h3).val.val
      rw [hmat, standardInvolution_val, GeneralLinearGroup.coe_scalar]
      simp only [Units.val_pow_eq_pow_val, Matrix.scalar_apply]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, hcancel, hneg]
    rw [he]
    exact mem_zpowers _

private lemma block_centralizer_projective (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj)
    (hchar : (2 : F) ≠ 0) (hc5 : ∀ x, J2.conj x = x ^ 5)
    (hnc : ¬ IsMulCommutative J2.specialSubgroup) :
    centralizer ((specialBlock J3 J2 h3 h2 hc).range : Set J3.specialSubgroup) ≤
      (zpowers (J3.specialToProjective (standardInvolution J3 h3))).comap
        J3.specialToProjective := by
  let b := blockEmbedding J3 J2 h3 h2 hc
  let f := specialBlock J3 J2 h3 h2 hc
  intro x hx
  have hz : x ∈ centralizer ({standardInvolution J3 h3} : Set J3.specialSubgroup) := by
    apply mem_centralizer_singleton_iff.mpr
    exact (mem_centralizer_iff.mp hx _
      (specialBlock_negativeTwo J3 J2 h3 h2 hc ▸
        show f (negativeTwo J2 h2) ∈ f.range from ⟨_, rfl⟩)).symm
  rw [← blockEmbedding_range J3 J2 h3 h2 hc hchar] at hz
  obtain ⟨A, rfl⟩ := hz
  have hA : A.val ∈ centralizer (J2.specialSubgroup : Set (GL (Fin 2) F)) := by
    intro y hy
    have h := mem_centralizer_iff.mp hx (f ⟨y, hy⟩) ⟨_, rfl⟩
    change b (Subgroup.inclusion J2.specialSubgroup_le_unitarySubgroup ⟨y, hy⟩) * b A =
      b A * b (Subgroup.inclusion J2.specialSubgroup_le_unitarySubgroup ⟨y, hy⟩) at h
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (blockEmbedding_injective J3 J2 h3 h2 hc h)
  obtain ⟨u, hu⟩ := GeneralLinearGroup.centralizer_le_scalar_of_noncommutative
    J2.specialSubgroup hnc hA
  exact scalar_block_projective J3 J2 h3 h2 hc hc5 A u hu

/-- Transport the residual-centralizer bound through a genuine group equivalence,
using the induced homomorphism on the full centralizers. -/
theorem residual_centralizer_bound_of_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (z : G)
    (h : let C := centralizer ({e z} : Set H)
      centralizer ((solvableResidual C).map C.subtype : Set H) ≤ zpowers (e z)) :
    let C := centralizer ({z} : Set G)
    centralizer ((solvableResidual C).map C.subtype : Set G) ≤ zpowers z := by
  let C := centralizer ({z} : Set G)
  let D := centralizer ({e z} : Set H)
  let c : D →* C :=
    { toFun y := ⟨e.symm y, mem_centralizer_singleton_iff.mpr (by
        apply e.injective
        simpa only [map_mul, e.apply_symm_apply] using
          mem_centralizer_singleton_iff.mp y.property)⟩
      map_one' := Subtype.ext e.symm.map_one
      map_mul' y w := Subtype.ext (e.symm.map_mul y w) }
  change centralizer ((solvableResidual C).map C.subtype : Set G) ≤ zpowers z
  intro x hx
  have hex : e x ∈ centralizer ((solvableResidual D).map D.subtype : Set H) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : c y ∈ solvableResidual C :=
      map_solvableResidual_le c (mem_map_of_mem c hy)
    have he := mem_centralizer_iff.mp hx (c y).val (mem_map_of_mem C.subtype hy')
    change e.symm y.val * x = x * e.symm y.val at he
    simpa only [map_mul, e.apply_symm_apply, Subgroup.subtype_apply] using congrArg e he
  obtain ⟨n, hn⟩ := h hex
  refine ⟨n, e.injective ?_⟩
  simpa only [map_zpow] using hn

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private lemma prime_conj (n : ℕ) (x : GaloisField 5 (2 * 1)) :
    (ABG.unitaryForm n 5 1 one_ne_zero).conj x = x ^ 5 := by
  simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]

private lemma standard_residual_centralizer_bound :
    let J := ABG.unitaryForm 3 5 1 one_ne_zero
    let z := J.specialToProjective (standardInvolution J rfl)
    let C := centralizer ({z} : Set (ProjectiveSpecialUnitaryMatrixGroup J))
    centralizer ((solvableResidual C).map C.subtype : Set
      (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ zpowers z := by
  let J3 := ABG.unitaryForm 3 5 1 one_ne_zero
  let J2 := ABG.unitaryForm 2 5 1 one_ne_zero
  let q := J3.specialToProjective
  let b := specialBlock J3 J2 rfl rfl rfl
  let K := b.range
  let z := standardInvolution J3 rfl
  let C := centralizer ({q z} : Set (ProjectiveSpecialUnitaryMatrixGroup J3))
  let e2 : J2.specialSubgroup ≃* SpecialLinearGroup (Fin 2) (ZMod 5) :=
    (ABG.specialUnitaryTwo_equiv_sl2 5 1 (by decide) (by decide)).trans
      (GorensteinWalter.sl2RingEquiv (GaloisField.equivZmodP 5).toRingEquiv)
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) (ZMod 5)) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod 5) (by simp)
  let : Group.IsPerfect J2.specialSubgroup :=
    Group.IsPerfect.ofSurjective (f := e2.symm.toMonoidHom) e2.symm.surjective
  let : Nontrivial (SpecialLinearGroup (Fin 2) (ZMod 5)) := by
    refine ⟨⟨1, -1, ?_⟩⟩
    intro he
    have hh := congrArg (fun A : SpecialLinearGroup (Fin 2) (ZMod 5) => A 0 0) he
    exact (by decide : (1 : ZMod 5) ≠ -1) (by simpa using hh)
  let : Nontrivial J2.specialSubgroup := e2.surjective.nontrivial
  let : Group.IsPerfect K := Group.IsPerfect.range b
  let : Group.IsPerfect (K.map q) := Group.IsPerfect.map q
  have hchar : (2 : GaloisField 5 (2 * 1)) ≠ 0 := by
    exact CharP.cast_ne_zero_of_ne_of_prime _ Nat.prime_two (by decide : 5 ≠ 2)
  have hle : K.map q ≤ C := by
    rintro _ ⟨x, ⟨a, rfl⟩, rfl⟩
    have hx : b a ∈ centralizer ({z} : Set J3.specialSubgroup) := by
      rw [← blockEmbedding_range J3 J2 rfl rfl rfl hchar]
      exact ⟨Subgroup.inclusion J2.specialSubgroup_le_unitarySubgroup a, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg q (mem_centralizer_singleton_iff.mp hx)
  have hr := le_map_solvableResidual_of_isPerfect (K.map q) C hle
  change centralizer ((solvableResidual C).map C.subtype : Set _) ≤ zpowers (q z)
  intro x hx
  obtain ⟨a, rfl⟩ := J3.specialToProjective_surjective x
  have ha : a ∈ centralizer (K : Set J3.specialSubgroup) := by
    rw [← comap_centralizer_map_eq_of_perfect q K
      (J3.specialToProjective_ker_le_center.trans (center_le_centralizer _))]
    exact centralizer_le hr hx
  exact block_centralizer_projective J3 J2 rfl rfl rfl hchar (prime_conj 2)
    (Group.IsPerfect.not_isMulCommutative J2.specialSubgroup) ha

private lemma standard_model_residual_centralizer_bound
    (t : ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 5 1 one_ne_zero))
    (ht : orderOf t = 2) :
    let C := centralizer ({t} : Set
      (ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 5 1 one_ne_zero)))
    centralizer ((solvableResidual C).map C.subtype : Set
      (ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 5 1 one_ne_zero))) ≤
        zpowers t := by
  let J := ABG.unitaryForm 3 5 1 one_ne_zero
  let q := J.specialToProjective
  have hcube : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x, hx⟩)
  obtain ⟨z, hz, rfl⟩ := InnerThreeRank.exists_involution_lift_of_cube_kernel q
    J.specialToProjective_surjective hcube t ht
  obtain ⟨g, hg⟩ := exists_special_involution_conjugator (p := 5) (by decide)
    (GaloisField.card 5 (2 * 1) (by decide)) J rfl (prime_conj 3) z hz
  let e := (MulAut.conj (q g)).symm
  have he : e (q z) = q (standardInvolution J rfl) := by
    have hq : MulAut.conj (q g) (q (standardInvolution J rfl)) = q z := by
      simpa only [MulAut.conj_apply, map_mul, map_inv] using congrArg q hg
    rw [← hq]
    exact (MulAut.conj (q g)).symm_apply_apply _
  apply residual_centralizer_bound_of_equiv e (q z)
  rw [he]
  exact standard_residual_centralizer_bound

/-- In every actual PSU₃(5) model, the centralizer of the embedded solvable
residual of an involution centralizer lies in the subgroup of that involution. -/
theorem residual_centralizer_bound (F : Type*) [Field F] [Finite F]
    (J : HermitianForm 3 F) (hcard : Nat.card F = 5 ^ 2)
    (hc : ∀ x, J.conj x = x ^ 5)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2) :
    let C := centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))
    centralizer ((solvableResidual C).map C.subtype : Set
      (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ zpowers t := by
  obtain ⟨e⟩ := InnerThreeRank.exists_projective_equiv_standard 5 F J hcard hc
  exact residual_centralizer_bound_of_equiv e t
    (standard_model_residual_centralizer_bound (e t) ((e.orderOf_eq t).trans ht))

end Matrix.SU3.FiveCentralizerRadical
