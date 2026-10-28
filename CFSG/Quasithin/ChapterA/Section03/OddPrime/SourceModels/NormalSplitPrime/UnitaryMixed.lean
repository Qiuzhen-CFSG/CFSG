module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.LinearExtension.TwistedNorm
public import Theory.SpecificGroups.SU3.NoncubicFieldActors
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms

/-!
# Cubic mixed unitary actors and the scalar determinant obstruction

Projective cubic descent applies to the literal unitary matrix acting on
PSU₃. A cubic coefficient acts trivially on the cyclic diagonal outer
quotient of order dividing three. Descent therefore forces the unitary
factor's determinant to be a cube. The norm-one correction makes that
factor inner, retaining the original actor and its coefficient.
Source: Aschbacher–Smith A.3.16–18, pp.51–53.
-/

@[expose] public noncomputable section
open Subgroup Matrix Theory.GroupTheory BenderSuzuki.MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open BenderSuzuki.MatrixGroups.HermitianForm
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.UnitaryMixed
open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem field_outer_commute (σ : F ≃+* F) (hs : σ ^ 3 = 1) (P : GL (Fin 3) F) :
    Commute (qOuter F (fieldAction F σ)) (qOuter F (linearConj F P)) := by
  let D := innerDiagonalOuter F
  let : IsCyclic D := isCyclic_range_of_ker_le_cyclic
    (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ) (linearOuterAction F)
      (det_ker_le_linearOuterAction_ker F)
  have hcard : Nat.card D ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨_, g, rfl⟩
    apply Subtype.ext
    change linearOuterAction F g ^ 3 = 1
    rw [linearOuterAction_eq_circleDiagonal_det]
    exact circleDiagonalOuter_cube _
  let b : normalizer (D : Set _) := ⟨qOuter F (fieldAction F σ),
    standardOuter_le_normalizer_innerDiagonalOuter
      ⟨fieldAction F σ, fieldAction_mem_standard F σ, rfl⟩⟩
  have hb : b ^ 3 = 1 := by
    apply Subtype.ext
    change qOuter F (fieldAction F σ) ^ 3 = 1
    rw [← map_pow, ← map_pow, hs, map_one, map_one]
  have hcop : Nat.Coprime 3 (Nat.card (MulAut D)) := by
    rw [IsCyclic.card_mulAut]
    rcases (Nat.dvd_prime Nat.prime_three).mp hcard with h | h
    · rw [h]; decide
    · rw [h]; decide
  have hact : D.normalizerMonoidHom b = 1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one (by rw [←map_pow,hb,map_one]))
      (orderOf_dvd_natCard _)
  have hh := congrArg (fun α : MulAut D => α ⟨linearOuterAction F P, ⟨P,rfl⟩⟩) hact
  exact (mul_inv_eq_iff_eq_mul).mp (congrArg Subtype.val hh)

omit [CharP F 2] in
private theorem det_cube (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hs : orderOf σ = 3) (ha : (linearConj F m * fieldAction F σ) ^ 3 = 1) :
    ∃ r : Fˣ, r ^ 3 = GeneralLinearGroup.det m := by
  obtain ⟨P, hP⟩ := Matrix.PSL3.StandardCubicFixedNine.Descent.exists_linear_conjugate_field
    m σ hs ha
  have hcomm := field_outer_commute σ (hs ▸ pow_orderOf_eq_one σ) P
  have hcongr : MulAut.congr (linearConj F P) (linearConj F m * fieldAction F σ) =
      linearConj F P * (linearConj F m * fieldAction F σ) * (linearConj F P)⁻¹ := by
    ext x
    simp only [MulAut.congr_apply,MulEquiv.trans_apply,MulAut.mul_apply]
    rfl
  have he := congrArg (qOuter F) hP
  rw [hcongr,map_mul,map_mul,map_inv] at he
  have he' : qOuter F (linearConj F m) * qOuter F (fieldAction F σ) =
      qOuter F (fieldAction F σ) := by
    apply mul_left_cancel (a := qOuter F (linearConj F P))
    rw [←hcomm.eq]
    exact (mul_inv_eq_iff_eq_mul).mp he
  have hm : qOuter F (linearConj F m) = 1 := by
    apply mul_right_cancel (b := qOuter F (fieldAction F σ))
    simpa only [one_mul] using he'
  exact (linearConj_inner_iff_det_cube m).mp ((QuotientGroup.eq_one_iff _).mp hm)

omit [CharP F 2] in
private theorem unitary_inner_of_det_cube
    (J : HermitianForm 3 F) {q : ℕ} (hq : q % 3 = 2)
    (hF : Nat.card F = q ^ 2) (hc : ∀ x, J.conj x = x ^ q)
    (u : J.unitarySubgroup) (hr : ∃ r : Fˣ, r ^ 3 = GeneralLinearGroup.det u.val) :
    J.unitaryConj u ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨r, hr⟩ := hr
  have hnorm : J.conj (r : F) * (r : F) = 1 := by
    have hqpos : 1 < q := by
      have hh := Finite.one_lt_card (α := F)
      rw [hF] at hh
      nlinarith
    have hcop : Nat.Coprime 3 (q-1) := Nat.prime_three.coprime_iff_not_dvd.mpr (by
      intro hd
      have hh := Nat.mod_eq_zero_of_dvd hd
      omega)
    have h3 : (r ^ (q+1)) ^ 3 = 1 := by
      rw [←pow_mul,Nat.mul_comm, pow_mul,hr]
      apply Units.ext
      have hh := J.unitary_det_norm_one u
      rw [hc,←pow_succ] at hh
      exact hh
    have hq1 : (r ^ (q+1)) ^ (q-1) = 1 := by
      rw [←pow_mul,show (q+1)*(q-1)=q^2-1 by simpa using (Nat.sq_sub_sq q 1).symm]
      rw [←hF,←Nat.card_units]
      exact pow_card_eq_one'
    have he : r ^ (q+1) = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
        (orderOf_dvd_of_pow_eq_one hq1))
    rw [hc,←pow_succ]
    exact congrArg Units.val he
  let v : J.specialSubgroup := ⟨GeneralLinearGroup.scalar (Fin 3) r⁻¹ * u.val, by
    refine ⟨J.unitarySubgroup.mul_mem (scalar_mem_unitary_of_norm_one J r⁻¹ ?_) u.property, ?_⟩
    · simp only [Units.val_inv_eq_inv_val,map_inv₀,←mul_inv,hnorm,inv_one]
    · change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) r⁻¹ * u.val) = 1
      simp only [map_mul,GeneralLinearGroup.det_scalar,Fintype.card_fin,inv_pow,hr,inv_mul_cancel]⟩
  have hv : (J.specialToProjective v).val = ProjGenLinGroup.mk u.val := by
    rw [J.specialToProjective_apply_val]
    simp only [v,map_mul,ProjGenLinGroup.mk_scalar,one_mul]
  refine ⟨J.specialToProjective v, ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change (J.specialToProjective v).val * x.val * (J.specialToProjective v).val⁻¹ = _
  rw [hv,J.unitaryConj_apply_val]

omit [Finite F] in
private theorem linear_cube_of_unitary_cube
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∃ t : F, J.conj t ≠ t)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (u : J.unitarySubgroup) (σ : F ≃+* F) (hs : σ ^ 3 = 1)
    (hu : ∀ x, (a x).val = ProjGenLinGroup.mk u.val *
      ProjGenLinGroup.map σ.toRingHom x.val * (ProjGenLinGroup.mk u.val)⁻¹)
    (ha : a ^ 3 = 1) : (linearConj F u.val * fieldAction F σ) ^ 3 = 1 := by
  let N := u.val * GeneralLinearGroup.map σ.toRingHom u.val *
    GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom u.val)
  have hs3 (x : ProjGenLinGroup (Fin 3) F) :
      ProjGenLinGroup.map σ.toRingHom (ProjGenLinGroup.map σ.toRingHom
        (ProjGenLinGroup.map σ.toRingHom x)) = x := by
    obtain ⟨v,rfl⟩ := ProjGenLinGroup.mk_surjective x
    simp only [ProjGenLinGroup.map_mk]
    congr 1
    apply Units.ext
    ext i j
    exact DFunLike.congr_fun hs (v.val i j)
  have hN : N ∈ center (GL (Fin 3) F) := by
    apply J.projective_centralizer_scalar hJ hconj
    intro x
    have hh := congrArg (fun b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) => (b x).val) ha
    change (a (a (a x))).val = x.val at hh
    rw [hu,hu,hu] at hh
    simp only [map_mul,map_inv] at hh
    rw [hs3] at hh
    apply (mul_inv_eq_iff_eq_mul).mp
    change ProjGenLinGroup.mk N * x.val * (ProjGenLinGroup.mk N)⁻¹ = x.val
    simpa only [N,map_mul,ProjGenLinGroup.map_mk,_root_.mul_inv_rev,mul_assoc] using hh
  have hn : linearConj F N = 1 := by
    change N ∈ (linearConj F).ker
    rwa [linearConj_ker]
  have he : (linearConj F u.val * fieldAction F σ) ^ 3 =
      linearConj F N * fieldAction F σ ^ 3 := by
    let L := linearConj F
    let S := fieldAction F σ
    change (L u.val * S) ^ 3 = _
    calc
      (L u.val * S) ^ 3 = L u.val * (S * L u.val) * (S * L u.val) * S := by
        simp only [pow_succ,pow_zero,one_mul,mul_assoc]
      _ = L u.val * (L (GeneralLinearGroup.map σ.toRingHom u.val) * S) *
          (L (GeneralLinearGroup.map σ.toRingHom u.val) * S) * S := by rw [field_linearConj]
      _ = (L u.val * L (GeneralLinearGroup.map σ.toRingHom u.val)) *
          (S * L (GeneralLinearGroup.map σ.toRingHom u.val)) * S * S := by group
      _ = _ := by
        rw [field_linearConj]
        simp only [N,L,S,map_mul,pow_succ,pow_zero,one_mul,mul_assoc]
  rw [he,hn,one_mul,←map_pow,hs,map_one]

/-- For a nontrivial cubic coefficient, the original cube-one unitary actor
has inner unitary factor. This is the literal mixed-actor nonsplitting step. -/
theorem inner_field_of_cube_one
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (ho : Odd n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hc : ∀ x, J.conj x = x ^ (2 ^ n))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (σ : F ≃+* F) (hs : orderOf σ = 3) (hf : J.HasUnitarySemilinearForm a σ)
    (ha : a ^ 3 = 1) :
    ∃ g : ProjectiveSpecialUnitaryMatrixGroup J,
      a = MulAut.conj g * ExtensionBorel.fieldActorHom J hJ σ := by
  obtain ⟨u,hu⟩ := hf
  have hconj : ∃ t : F, J.conj t ≠ t := by
    by_contra! h
    have he : Nat.card {x : F // J.conj x = x} = Nat.card F :=
      Nat.card_congr (Equiv.subtypeUnivEquiv h)
    rw [FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hc,hF] at he
    have hp : 1 < 2^n := one_lt_pow₀ (by decide) (by omega)
    nlinarith
  have hmod : 2 ^ n % 3 = 2 := by
    rw [Nat.BinaryTorusParity.two_pow_mod_three, if_neg]
    have hh := Nat.odd_iff.mp ho
    omega
  obtain ⟨g,hg⟩ := unitary_inner_of_det_cube J hmod hF hc u
    (det_cube u.val σ hs (linear_cube_of_unitary_cube J hJ hconj a u σ
      (hs ▸ pow_orderOf_eq_one σ) hu ha))
  refine ⟨g, ?_⟩
  rw [hg]
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [MulAut.mul_apply,J.unitaryConj_apply_val]
  simpa only [ExtensionBorel.fieldActorHom,MonoidHom.coe_mk,OneHom.coe_mk,
    ExtensionBorel.fieldActor_apply_val] using hu x

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.UnitaryMixed
