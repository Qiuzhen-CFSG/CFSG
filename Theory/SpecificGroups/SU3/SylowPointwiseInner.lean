module

public import Theory.SpecificGroups.SU3.EvenSemilinear
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.RootNormalizer
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Involutive pointwise Sylow fixers in binary PSU₃

For the actual projective Hermitian root group, a unitary-semilinear map
fixing every root element has trivial field parameter. Root normalization
makes the unitary representative triangular. Trace one removes projective
scalar ambiguity, and the (0,1) matrix entry, as the first root coordinate
ranges over the whole quadratic field, detects every field element.

Binary semilinear coverage and the exponent-three diagonal quotient then
make every square-one Sylow fixer inner. Sylow conjugacy supplies every
Sylow subgroup. Simplicity is inherited from the caller.

The matrix calculation adapts the root part of the proof in
`SU3/BorelTorus/SemilinearFixer.lean`, without its torus-fixing hypothesis.
Sources: Huppert II.10.12; GLS3, Theorem 2.5.12 and §2.7;
Aschbacher–Smith, combined manuscript of 1 March 2004, proof of 13.6.6,
printed p.927, and Lemma 16.1.6, printed p.1172.
-/

public section

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.SylowPointwiseInner
open OddPrimeSylow.NormalizedOuter.Coverage BorelTorus.SemilinearActors
variable {E : Type*} [Field E] [Finite E] [CharP E 2]

omit [Finite E] [CharP E 2] in
private theorem untwist (A X Y : GL (Fin 3) E)
    (hX : X.val.trace = 1) (hY : Y.val.trace = 1)
    (h : ProjGenLinGroup.mk (A * Y * A⁻¹) = ProjGenLinGroup.mk X) :
    A.val * Y.val = X.val * A.val := by
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have ht := congrArg (fun B : GL (Fin 3) E => B.val.trace) hc
  have hm : ((A * Y * A⁻¹) * GeneralLinearGroup.scalar (Fin 3) c).val =
      (c : E) • (A.val * Y.val * (A⁻¹).val) := by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal, mul_comm]
  rw [hm, trace_smul, trace_units_conj, hX, hY, smul_eq_mul, mul_one] at ht
  have hc1 : c = 1 := Units.ext ht
  rw [hc1, map_one, mul_one] at hc
  exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp hc)

/-- Pointwise fixation of the full Hermitian root group detects the field parameter. -/
theorem semilinear_fixing_root_field_eq_one
    (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (σ : E ≃+* E) (hsem : J.HasUnitarySemilinearForm a σ)
    (hfix : ∀ z : hermitianUnipotentCoord J,
      a (root J hJ z) = root J hJ z) : σ = 1 := by
  obtain ⟨u, hu⟩ := hsem
  have hroot : (BorelTorus.projectiveRoot J hJ).map a.toMonoidHom =
      BorelTorus.projectiveRoot J hJ := by
    apply le_antisymm
    · rintro x ⟨z, ⟨t, rfl⟩, hzx⟩
      exact ⟨t, (hfix t).symm.trans hzx⟩
    · rintro x ⟨t, rfl⟩
      exact ⟨root J hJ t, ⟨t, rfl⟩, hfix t⟩
  obtain ⟨h10, h20, h21⟩ :=
    projective_semilinear_upper J hJ hcard hfixed a σ u hu hroot
  have htrace (z : hermitianUnipotentCoord J) :
      (hermitianUnipotentGL J z).val.trace = 1 := by
    simp [hermitianUnipotentGL, hermitianUnipotentMatrix, Matrix.trace,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  have hmat (z : hermitianUnipotentCoord J) :
      u.val.val * (GeneralLinearGroup.map σ.toRingHom
        (hermitianUnipotentGL J z)).val =
        (hermitianUnipotentGL J z).val * u.val.val := by
    apply untwist u.val (hermitianUnipotentGL J z)
      (GeneralLinearGroup.map σ.toRingHom (hermitianUnipotentGL J z))
      (htrace z) (by
        change Matrix.trace ((hermitianUnipotentGL J z).val.map σ) = 1
        rw [← AddMonoidHom.map_trace, htrace, map_one])
    have hh := hu (root J hJ z)
    rw [hfix z] at hh
    simpa only [root, hermitianUnipotentPSU_val, ProjGenLinGroup.map_mk,
      map_mul, map_inv] using hh.symm
  have hentry (x : E) : u.val.val 0 0 * σ x = x * u.val.val 1 1 := by
    obtain ⟨z, hz⟩ := EvenSemilinear.coord_first_surjective J hcard hfixed x
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) (hmat z)
    rw [field_map_root] at hh
    simp [hermitianUnipotentMatrix, rootFieldEquiv_val,
      Matrix.mul_apply, Fin.sum_univ_three, h21, hz] at hh
    linear_combination hh
  have hdiag : u.val.val 0 0 = u.val.val 1 1 := by simpa using hentry 1
  have h00 : u.val.val 0 0 ≠ 0 := by
    intro hz
    have hd := u.val.det_ne_zero
    simp [Matrix.det_fin_three, h10, h20, h21, hz] at hd
  apply RingEquiv.ext
  intro x
  change σ x = x
  apply mul_left_cancel₀ h00
  simpa only [← hdiag, mul_comm] using hentry x

/-- The remaining diagonal image has exponent three, so a square-one root fixer is inner. -/
theorem involutive_fixing_root_inner
    (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (hfix : ∀ z : hermitianUnipotentCoord J,
      a (root J hJ z) = root J hJ z) :
    ∃ b, a = MulAut.conj b := by
  obtain ⟨σ, hσ⟩ := EvenSemilinear.semilinear_coverage J hJ hn hcard hconj a
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  have he := semilinear_fixing_root_field_eq_one J hJ hcard hfixed a σ hσ hfix
  rw [he] at hσ
  obtain ⟨u, rfl⟩ := (HasUnitarySemilinearForm.one_iff J).mp hσ
  exact J.unitaryConj_is_inner_of_sq_eq_one u ha

/-- Every square-one automorphism fixing a Sylow two-subgroup pointwise is inner. -/
theorem involutive_fixing_sylow_inner
    (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (hfix : ∀ x ∈ S, a x = x) : ∃ b, a = MulAut.conj b := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  let P := EvenTwoRank.rootSylow J hJ (by omega) hcard hfixed
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (ProjectiveSpecialUnitaryMatrixGroup J) S P
  let e := MulAut.conj g
  have hmap : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom = P :=
    congrArg Sylow.toSubgroup hg
  have hp : MulAut.congr e a ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have hf : ∀ z : hermitianUnipotentCoord J,
      MulAut.congr e a (root J hJ z) = root J hJ z := by
    intro z
    have hz : root J hJ z ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
        e.toMonoidHom := by
      rw [hmap]
      exact ⟨z, rfl⟩
    obtain ⟨x, hx, he⟩ := hz
    rw [← he]
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply, hfix x hx]
  obtain ⟨b, hb⟩ := involutive_fixing_root_inner J hJ hn hcard hconj
    (MulAut.congr e a) hp hf
  refine ⟨e.symm b, (MulAut.congr e).injective ?_⟩
  rw [MulAut.congr_conj, e.apply_symm_apply]
  exact hb

end BenderSuzuki.MatrixGroups.HermitianForm.SylowPointwiseInner
