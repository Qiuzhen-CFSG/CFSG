module
public import Theory.SpecificGroups.SU3.EvenSemilinear
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.RootNormalizer
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Involutive Hermitian actors with square-one root displacements

A root-normalizing semilinear actor with square-one root displacements acts
trivially on the first root coordinate. Its unitary representative is upper
triangular. Trace one removes scalar ambiguity, and the (0,1) matrix entry
then forces every field element to be fixed. Binary semilinear coverage and
the odd diagonal quotient make each such involutive actor inner. Sylow
conjugacy supplies the same detector for every prescribed Sylow subgroup.

Source: Aschbacher–Smith E.2.7, printed p.218, normal unitary Bender case;
Hermitian root coordinates from Huppert II.10.12 and GLS3, Theorem 2.5.12.
-/

public section

open Matrix BenderSuzuki.External Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.SylowQuadraticInner
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

/-- Square-one root displacements detect the field parameter. -/
theorem semilinear_root_displacement_field_eq_one
    (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (σ : E ≃+* E) (hsem : J.HasUnitarySemilinearForm a σ)
    (hroot : (BorelTorus.projectiveRoot J hJ).map a.toMonoidHom = BorelTorus.projectiveRoot J hJ)
    (hfix : ∀ z : hermitianUnipotentCoord J,
      ((root J hJ z)⁻¹ * a (root J hJ z)) ^ 2 = 1) : σ = 1 := by
  obtain ⟨u,hu⟩ := hsem
  obtain ⟨h10,h20,h21⟩ :=
    projective_semilinear_upper J hJ hcard hfixed a σ u hu hroot
  have htrace (z : hermitianUnipotentCoord J) :
      (hermitianUnipotentGL J z).val.trace = 1 := by
    simp [hermitianUnipotentGL,hermitianUnipotentMatrix,Matrix.trace,
      Fin.sum_univ_three,CharTwo.add_self_eq_zero]
  have himage (z : hermitianUnipotentCoord J) : ∃ w : hermitianUnipotentCoord J,
      a (root J hJ z) = root J hJ w ∧ w.val.1 = z.val.1 := by
    have hr := mem_map_of_mem a.toMonoidHom
      (show root J hJ z ∈ BorelTorus.projectiveRoot J hJ from ⟨z,rfl⟩)
    rw [hroot] at hr
    obtain ⟨w,hw⟩ := hr
    change root J hJ w = a (root J hJ z) at hw
    refine ⟨w,hw.symm,?_⟩
    have hsq : (z⁻¹ * w)^2 = 1 := by
      apply root_injective J hJ
      rw [map_pow,map_mul,map_inv,map_one]
      rw [hw]
      exact hfix z
    have hzero := (EvenSemilinear.square_eq_one_iff_first_zero J _).mp hsq
    change -z.val.1 + w.val.1 = 0 at hzero
    exact (neg_add_eq_zero.mp hzero).symm
  have hmat (z w : hermitianUnipotentCoord J) (hw : a (root J hJ z) = root J hJ w) :
      u.val.val * (GeneralLinearGroup.map σ.toRingHom (hermitianUnipotentGL J z)).val =
        (hermitianUnipotentGL J w).val * u.val.val := by
    apply untwist u.val (hermitianUnipotentGL J w)
      (GeneralLinearGroup.map σ.toRingHom (hermitianUnipotentGL J z))
      (htrace w) (by
        change Matrix.trace ((hermitianUnipotentGL J z).val.map σ) = 1
        rw [← AddMonoidHom.map_trace,htrace,map_one])
    have hh := hu (root J hJ z)
    rw [hw] at hh
    simpa only [root,hermitianUnipotentPSU_val,ProjGenLinGroup.map_mk,map_mul,map_inv] using hh.symm
  have hentry (x : E) : u.val.val 0 0 * σ x = x * u.val.val 1 1 := by
    obtain ⟨z,hz⟩ := EvenSemilinear.coord_first_surjective J hcard hfixed x
    obtain ⟨w,hw,hwz⟩ := himage z
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) (hmat z w hw)
    rw [field_map_root] at hh
    simp [hermitianUnipotentMatrix,rootFieldEquiv_val,
      Matrix.mul_apply,Fin.sum_univ_three,h21,hwz,hz] at hh
    linear_combination hh
  have hdiag : u.val.val 0 0 = u.val.val 1 1 := by simpa using hentry 1
  have h00 : u.val.val 0 0 ≠ 0 := by
    intro hz
    have hd := u.val.det_ne_zero
    simp [Matrix.det_fin_three,h10,h20,h21,hz] at hd
  apply RingEquiv.ext
  intro x
  change σ x = x
  apply mul_left_cancel₀ h00
  simpa only [← hdiag,mul_comm] using hentry x

/-- A square-one actor with square-one root displacements is inner. -/
theorem involutive_root_displacement_inner
    (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (hroot : (BorelTorus.projectiveRoot J hJ).map a.toMonoidHom = BorelTorus.projectiveRoot J hJ)
    (hfix : ∀ z : hermitianUnipotentCoord J,
      ((root J hJ z)⁻¹ * a (root J hJ z)) ^ 2 = 1) :
    ∃ b, a = MulAut.conj b := by
  obtain ⟨σ,hσ⟩ := EvenSemilinear.semilinear_coverage J hJ hn hcard hconj a
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  have he := semilinear_root_displacement_field_eq_one J hJ hcard hfixed a σ hσ hroot hfix
  rw [he] at hσ
  obtain ⟨u,rfl⟩ := (HasUnitarySemilinearForm.one_iff J).mp hσ
  exact J.unitaryConj_is_inner_of_sq_eq_one u ha

/-- The same detector for the prescribed arbitrary Sylow subgroup. -/
theorem involutive_sylow_displacement_inner
    (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map a.toMonoidHom = S)
    (hfix : ∀ x ∈ S, (x⁻¹ * a x)^2 = 1) : ∃ b, a = MulAut.conj b := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  let P := EvenTwoRank.rootSylow J hJ (by omega) hcard hfixed
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S P
  let e := MulAut.conj g
  have hmap : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom = P :=
    congrArg Sylow.toSubgroup hg
  have hp : MulAut.congr e a ^ 2 = 1 := by rw [← map_pow,ha,map_one]
  have hr : (BorelTorus.projectiveRoot J hJ).map (MulAut.congr e a).toMonoidHom =
      BorelTorus.projectiveRoot J hJ := by
    change (P : Subgroup _).map (MulAut.congr e a).toMonoidHom = P
    rw [←hmap]
    have he : (MulAut.congr e a).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp a.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change e (a (e.symm (e x))) = e (a x)
      rw [e.symm_apply_apply]
    rw [Subgroup.map_map,he,←Subgroup.map_map,hS]
  have hf : ∀ z : hermitianUnipotentCoord J,
      ((root J hJ z)⁻¹ * MulAut.congr e a (root J hJ z))^2 = 1 := by
    intro z
    have hz : root J hJ z ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
        e.toMonoidHom := by rw [hmap]; exact ⟨z,rfl⟩
    obtain ⟨x,hx,he⟩ := hz
    rw [←he]
    change ((e x)⁻¹ * e (a (e.symm (e x))))^2 = 1
    rw [e.symm_apply_apply,←map_inv,←map_mul,←map_pow,hfix x hx,map_one]
  obtain ⟨b,hb⟩ := involutive_root_displacement_inner J hJ hn hcard hconj
    (MulAut.congr e a) hp hr hf
  refine ⟨e.symm b,(MulAut.congr e).injective ?_⟩
  rw [MulAut.congr_conj,e.apply_symm_apply]
  exact hb

end BenderSuzuki.MatrixGroups.HermitianForm.SylowQuadraticInner
