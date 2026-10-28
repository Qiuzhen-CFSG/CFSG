module

public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.RootNormalizer
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.TorusAction
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.DiagonalActors
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Semilinear
public import Theory.SpecificGroups.SU3.OuterSolvable
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.GroupTheory.Sylow

open Matrix
open BenderSuzuki.External
open scoped MatrixGroups

namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus

variable {E : Type*} [Field E] [Finite E]

omit [Finite E] in
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

private theorem fixed_root_upper
    (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (σ : E ≃+* E) (u : J.unitarySubgroup)
    (hu : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk u.val *
        ProjGenLinGroup.map σ.toRingHom x.val * (ProjGenLinGroup.mk u.val)⁻¹)
    (hfix : ∀ z : hermitianUnipotentCoord J,
      a (hermitianUnipotentPSU J hJ z) = hermitianUnipotentPSU J hJ z) :
    u.val.val 1 0 = 0 ∧ u.val.val 2 0 = 0 ∧ u.val.val 2 1 = 0 := by
  apply SemilinearActors.projective_semilinear_upper J hJ hcard hfixed a σ u hu
  apply le_antisymm
  · rintro x ⟨z, hz, hzx⟩
    obtain ⟨t, rfl⟩ := hz
    have hx : x = hermitianUnipotentPSU J hJ t := hzx.symm.trans (hfix t)
    rw [hx]
    exact ⟨t, rfl⟩
  · rintro x ⟨t, rfl⟩
    exact ⟨hermitianUnipotentPSU J hJ t, ⟨t, rfl⟩, hfix t⟩

private theorem fixed_root_identity
    (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (σ : E ≃+* E) (u : J.unitarySubgroup)
    (hu : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk u.val *
        ProjGenLinGroup.map σ.toRingHom x.val * (ProjGenLinGroup.mk u.val)⁻¹)
    (hfixroot : ∀ z : hermitianUnipotentCoord J,
      a (hermitianUnipotentPSU J hJ z) = hermitianUnipotentPSU J hJ z)
    (hfixtorus : ∀ k : Eˣ,
      a (hermitianTorusPSU J hJ k) = hermitianTorusPSU J hJ k) :
    a = 1 := by
  let : Fintype E := Fintype.ofFinite E
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [pow_mul] using hcard)
  obtain ⟨h10, h20, h21⟩ := fixed_root_upper J hJ hcard hfixed a σ u hu hfixroot
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
    have hh := hu (hermitianUnipotentPSU J hJ z)
    rw [hfixroot z] at hh
    simpa only [hermitianUnipotentPSU_val, ProjGenLinGroup.map_mk,
      map_mul, map_inv] using hh.symm
  have hσ : σ = 1 := by
    apply RingEquiv.ext
    intro x
    obtain ⟨y, hy⟩ := huppert_II_10_4_trace_surjective J (2 ^ n)
      hcard hfixed (-(x * J.conj x)) (by
        rw [map_neg, map_mul, J.conj_involutive]
        ring)
    let z : hermitianUnipotentCoord J := ⟨(x, y), by
      dsimp only
      rw [hy]
      ring⟩
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) (hmat z)
    rw [SemilinearActors.field_map_root] at hh
    simp [hermitianUnipotentMatrix, SemilinearActors.rootFieldEquiv_val,
      Matrix.mul_apply, Fin.sum_univ_three, h21] at hh
    have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1)
      (hmat ⟨(1, Classical.choose (huppert_II_10_4_trace_surjective J (2 ^ n)
        hcard hfixed (-((1 : E) * J.conj 1)) (by
          rw [map_neg, map_mul, J.conj_involutive]
          ring))), by
        dsimp only
        rw [Classical.choose_spec (huppert_II_10_4_trace_surjective J (2 ^ n)
          hcard hfixed (-((1 : E) * J.conj 1)) (by
            rw [map_neg, map_mul, J.conj_involutive]
            ring))]
        simp⟩)
    rw [SemilinearActors.field_map_root] at h1
    simp [hermitianUnipotentMatrix, SemilinearActors.rootFieldEquiv_val,
      Matrix.mul_apply, Fin.sum_univ_three, h21] at h1
    have hdiag : u.val.val 0 0 = u.val.val 1 1 := by
      linear_combination h1
    have h00 : u.val.val 0 0 ≠ 0 := by
      intro hz
      have hd := u.val.det_ne_zero
      simp [Matrix.det_fin_three, h10, h20, h21, hz] at hd
    have hσx : u.val.val 0 0 * σ x = u.val.val 1 1 * x := by
      linear_combination hh
    apply mul_left_cancel₀ h00
    rw [← hdiag] at hσx
    simpa using hσx
  subst σ
  obtain ⟨y1, hy1⟩ := huppert_II_10_4_trace_surjective J (2 ^ n)
    hcard hfixed (-((1 : E) * J.conj 1)) (by
      rw [map_neg, map_mul, J.conj_involutive]
      ring)
  let z1 : hermitianUnipotentCoord J := ⟨(1, y1), by
    dsimp only
    rw [hy1]
    simp⟩
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 2) (hmat z1)
  simp [hermitianUnipotentMatrix, Matrix.mul_apply, Fin.sum_univ_three, h10, z1] at h12
  have hdiag2 : u.val.val 1 1 = u.val.val 2 2 := by
    have h12' := h12
    simp only [CharTwo.neg_eq] at h12'
    linear_combination h12'
  have h01d := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1)
    (hmat z1)
  simp [hermitianUnipotentMatrix, Matrix.mul_apply, Fin.sum_univ_three, h21, z1] at h01d
  have hdiag : u.val.val 0 0 = u.val.val 1 1 := by
    linear_combination h01d
  have hconjne : ∃ t : E, J.conj t ≠ t := by
    by_contra h
    apply (J.conj_ne_one_of_card n hn hcard hfixed)
    ext t
    by_contra ht
    exact h ⟨t, ht⟩
  obtain ⟨t, ht⟩ := hconjne
  obtain ⟨yt, hyt⟩ := huppert_II_10_4_trace_surjective J (2 ^ n)
    hcard hfixed (-(t * J.conj t)) (by
      rw [map_neg, map_mul, J.conj_involutive]
      ring)
  let zt : hermitianUnipotentCoord J := ⟨(t, yt), by
    dsimp only
    rw [hyt]
    ring⟩
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2) (hmat zt)
  simp [hermitianUnipotentMatrix, Matrix.mul_apply, Fin.sum_univ_three, zt] at h02
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2) (hmat z1)
  simp [hermitianUnipotentMatrix, Matrix.mul_apply, Fin.sum_univ_three, z1] at h01
  rw [hdiag, hdiag2] at h01 h02
  have hrel : u.val.val 0 1 + u.val.val 1 2 = 0 := by
    have h01' := h01
    have h01'' := congrArg (fun q : E => q - (u.val.val 2 2 * y1 + u.val.val 0 2)) h01'
    have htmp : -u.val.val 0 1 = u.val.val 1 2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm] using h01''
    calc
      u.val.val 0 1 + u.val.val 1 2 = u.val.val 0 1 + (-u.val.val 0 1) := by rw [← htmp]
      _ = 0 := add_neg_cancel _
  have hu01 : u.val.val 0 1 = 0 := by
    have hrel' : (J.conj t + t) * u.val.val 0 1 = 0 := by
      have h02' := h02
      have h01' := h01
      have hu12eq : u.val.val 1 2 = u.val.val 0 1 := by
        have hneg : u.val.val 0 1 = -u.val.val 1 2 :=
          eq_neg_of_add_eq_zero_left hrel
        simpa [CharTwo.neg_eq] using hneg.symm
      rw [hu12eq] at h02' h01'
      have h02'' := congrArg (fun q : E => q - (u.val.val 2 2 * yt + u.val.val 0 2)) h02'
      have htmp : -(u.val.val 0 1) * J.conj t = t * u.val.val 0 1 := by
        simpa [mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm] using h02''
      linear_combination -htmp
    have hsum : J.conj t + t ≠ 0 := by
      intro hz
      apply ht
      have hz' : J.conj t = -t := eq_neg_of_add_eq_zero_left hz
      simpa [CharTwo.neg_eq] using hz'
    exact (mul_eq_zero.mp hrel').resolve_left hsum
  have hu12 : u.val.val 1 2 = 0 := by
    rw [← hrel]
    simp [hu01]
  have hshape : u.val.val = !![u.val.val 0 0, 0, u.val.val 0 2;
      0, u.val.val 0 0, 0; 0, 0, u.val.val 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h10, h20, h21, hdiag, hdiag2, hu01, hu12]
  have htorus (k : Eˣ) :
      ProjGenLinGroup.mk (u.val * hermitianTorusGL J k) =
        ProjGenLinGroup.mk (hermitianTorusGL J k * u.val) := by
    have hh := hu (hermitianTorusPSU J hJ k)
    rw [hfixtorus k] at hh
    rw [hermitianTorusPSU_val] at hh
    change ProjGenLinGroup.mk (hermitianTorusGL J k) =
      ProjGenLinGroup.mk u.val *
        ProjGenLinGroup.map (RingHom.id E)
          (ProjGenLinGroup.mk (hermitianTorusGL J k)) *
        (ProjGenLinGroup.mk u.val)⁻¹ at hh
    rw [ProjGenLinGroup.map_id, MonoidHom.id_apply] at hh
    have hh' := congrArg (fun q => q * ProjGenLinGroup.mk u.val) hh
    simpa only [map_mul, mul_assoc, inv_mul_cancel, mul_one] using hh'.symm
  have htorus_entry (k : Eˣ) :
      u.val.val 0 2 * (k : E) = (J.conj (k : E))⁻¹ * u.val.val 0 2 := by
    obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp (htorus k)
    have hc00 := congrArg (fun M : GL (Fin 3) E => M.val 0 0) hc
    have hc02 := congrArg (fun M : GL (Fin 3) E => M.val 0 2) hc
    have hdiag_nonzero : u.val.val 0 0 ≠ 0 := by
      intro hz
      have hd := u.val.det_ne_zero
      rw [hshape] at hd
      simp [Matrix.det_fin_three, hz] at hd
    have hk0 : J.conj (k : E) ≠ 0 := (map_ne_zero J.conj).2 (Units.ne_zero k)
    have hc1 : c = 1 := by
      apply Units.ext
      have he : u.val.val 0 0 * (J.conj (k : E))⁻¹ * (c : E) =
          (J.conj (k : E))⁻¹ * u.val.val 0 0 := by
        simpa [GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
          Fin.sum_univ_three, hermitianTorusMatrix, h10, h20, h21,
          hdiag, hdiag2, hu01, hu12] using hc00
      apply mul_left_cancel₀ (mul_ne_zero hdiag_nonzero (inv_ne_zero hk0))
      simpa [mul_assoc, mul_comm, mul_left_comm] using he
    rw [hc1, map_one, mul_one] at hc02
    simpa [GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_three, hermitianTorusMatrix, h10, h20, h21,
      hdiag, hdiag2, hu01, hu12] using hc02
  by_cases hu02 : u.val.val 0 2 = 0
  · have huval : u.val.val = u.val.val 0 0 • (1 : Matrix (Fin 3) (Fin 3) E) := by
      rw [hshape, hu02]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
    have hdiag_nonzero : u.val.val 0 0 ≠ 0 := by
      intro hz
      have hd := u.val.det_ne_zero
      rw [hshape] at hd
      simp [Matrix.det_fin_three, hz] at hd
    have hmk : ProjGenLinGroup.mk u.val = 1 := by
      apply ProjGenLinGroup.mk_eq_one.mpr
      apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
      refine ⟨Units.mk0 (u.val.val 0 0) ?_, ?_⟩
      · exact hdiag_nonzero
      · simpa [GeneralLinearGroup.coe_scalar, ← smul_one_eq_diagonal] using huval.symm
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [hu]
    change ProjGenLinGroup.mk u.val *
      ProjGenLinGroup.map (RingHom.id E) x.val *
      (ProjGenLinGroup.mk u.val)⁻¹ = x.val
    rw [ProjGenLinGroup.map_id, MonoidHom.id_apply]
    simp [hmk]
  · have hnormall : EvenInner.normOne J = ⊤ := by
      ext k
      change J.conj (k : E) = (k : E)⁻¹ ↔ _
      constructor
      · intro hk
        exact trivial
      · intro _
        have h := htorus_entry k
        have hk0 : J.conj (k : E) ≠ 0 := (map_ne_zero J.conj).2 (Units.ne_zero k)
        have hh := congrArg (fun q : E => q * J.conj (k : E)) h
        have hprod : (k : E) * J.conj (k : E) = 1 := by
          apply mul_left_cancel₀ hu02
          simpa [mul_assoc, mul_comm, mul_left_comm, hk0] using hh
        exact (mul_eq_one_iff_eq_inv₀ (Units.ne_zero k)).mp
          (by simpa [mul_comm] using hprod)
    have hcardnorm := EvenInner.normOne_card J hcard hconj
    rw [hnormall, Subgroup.card_top, Nat.card_units, hcard] at hcardnorm
    have hcardnorm' : (2 ^ n) ^ 2 = 2 ^ n + 2 := by
      have hbase : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
      have hq2 : 1 ≤ (2 ^ n) ^ 2 := one_le_pow₀ hbase
      omega
    have hq : 4 ≤ 2 ^ n := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := by exact pow_le_pow_right₀ (by norm_num) hn
    nlinarith [hcardnorm']

private theorem torus_mem_root_sylow_normalizer
    (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (k : Eˣ) :
    hermitianTorusPSU J hJ k ∈ Subgroup.normalizer
      ((EvenTwoRank.rootSylow J hJ (by omega) hcard hfixed :
        Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) : Set
          (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let P := EvenTwoRank.rootSylow J hJ (by omega) hcard hfixed
  have hP : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
      projectiveRoot J hJ := by
    rw [EvenTwoRank.rootSylow_coe]
    rfl
  have hPset : (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      (projectiveRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    exact congrArg (fun H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) =>
      (H : Set (ProjectiveSpecialUnitaryMatrixGroup J))) hP
  rw [hPset]
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨z, rfl⟩
  refine ⟨hermitianTorusAction J k z, ?_⟩
  rw [hermitianTorusPSU_mul_unipotent, mul_assoc, mul_inv_cancel, mul_one]

/-- A unitary-semilinear involution fixing the normalizer of a Sylow two-subgroup
of the binary projective unitary model is trivial. The formula is kept in the
actual projective matrix image, with an arbitrary field parameter and unitary
representative. -/
public theorem unitary_semilinear_fixer_eq_one
    (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (σ : E ≃+* E)
    (hsem : J.HasUnitarySemilinearForm a σ)
    (_ha2 : a ^ 2 = 1)
    (hfix : ∀ b ∈ Subgroup.normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      a b = b) :
    a = 1 := by
  let : Fintype E := Fintype.ofFinite E
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [pow_mul] using hcard)
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let P := EvenTwoRank.rootSylow J hJ (by omega) hcard
    (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj)
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (ProjectiveSpecialUnitaryMatrixGroup J) S P
  let e : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) := MulAut.conj g
  have heP : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom = P := by
    exact congrArg Sylow.toSubgroup hg
  have hnorm_map :
      (Subgroup.normalizer (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).map
          e.toMonoidHom =
        Subgroup.normalizer (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [← heP]
    exact Subgroup.map_equiv_normalizer_eq
      (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) e
  let b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) := e * a * e⁻¹
  have hfixP : ∀ x ∈ (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), b x = x := by
    intro x hx
    have hx' : x ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom := by
      rw [heP]
      exact hx
    obtain ⟨y, hy, hxy⟩ := hx'
    have hay : a y = y := hfix y (S.le_normalizer hy)
    rw [← hxy]
    simp [b, hay]
  have hfixPnorm : ∀ x ∈ Subgroup.normalizer
      (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)), b x = x := by
    intro x hx
    have hx' : x ∈ (Subgroup.normalizer
        (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).map e.toMonoidHom := by
      rw [hnorm_map]
      exact hx
    obtain ⟨y, hy, hxy⟩ := hx'
    have hay : a y = y := hfix y hy
    rw [← hxy]
    simp [b, hay]
  obtain ⟨x, hx⟩ := J.specialToProjective_surjective g
  let ug : J.unitarySubgroup := ⟨x.val, x.property.1⟩
  have heq : J.unitaryConj ug = e := by
    simpa [ug, e, hx] using J.unitaryConj_special_is_inner x
  have hform_e : J.HasUnitarySemilinearForm e 1 := by
    apply (HasUnitarySemilinearForm.one_iff J).2
    exact ⟨ug, heq.symm⟩
  have hunit_inv : J.unitaryConj (ug⁻¹) = (J.unitaryConj ug)⁻¹ := by
    simpa only [J.unitaryConjHom_apply] using (map_inv J.unitaryConjHom ug)
  have hform_einv : J.HasUnitarySemilinearForm e⁻¹ 1 := by
    apply (HasUnitarySemilinearForm.one_iff J).2
    refine ⟨ug⁻¹, ?_⟩
    calc
      e⁻¹ = (J.unitaryConj ug)⁻¹ := by rw [heq]
      _ = J.unitaryConj (ug⁻¹) := hunit_inv.symm
  have hform_b : J.HasUnitarySemilinearForm b σ := by
    simpa [b] using ((hform_e.mul J hJ hsem).mul J hJ hform_einv)
  have hPcoe : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
      projectiveRoot J hJ := by
    rw [EvenTwoRank.rootSylow_coe]
    rfl
  have hfixroot : ∀ z : hermitianUnipotentCoord J,
      b (hermitianUnipotentPSU J hJ z) = hermitianUnipotentPSU J hJ z := by
    intro z
    apply hfixP
    rw [hPcoe]
    exact ⟨z, rfl⟩
  have hfixtorus : ∀ k : Eˣ,
      b (hermitianTorusPSU J hJ k) = hermitianTorusPSU J hJ k := by
    intro k
    apply hfixPnorm
    exact torus_mem_root_sylow_normalizer J hJ hn hcard hfixed k
  obtain ⟨u, hu⟩ := hform_b
  have hb : b = 1 := fixed_root_identity J hJ hn hcard hfixed hconj b σ u hu
    hfixroot hfixtorus
  calc
    a = e⁻¹ * (e * a * e⁻¹) * e := by group
    _ = 1 := by rw [show e * a * e⁻¹ = b from rfl, hb]; simp

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
