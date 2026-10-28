module

public import Theory.SpecificGroups.SU3.UnitaryEight.Reduction
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear centralizers of outer cubics in PGU₃(8)

An outer projective cubic in the genuine ternary unitary group has no
nonidentity projective involution in its linear centralizer. The proof works
for every nondegenerate ternary Hermitian form over the field of order 64
with fixed field of order 8, hence in particular for the antidiagonal form.

In characteristic two, a matrix whose square is scalar has nonzero trace.
Taking traces removes the scalar ambiguity in projective commutation. If its
projective class is nontrivial, subtracting its trace times the identity gives
a nonzero square-zero map. Its image is one-dimensional, so a commuting matrix
has an eigenvector there. For a projective cubic this eigenvalue makes the
scalar cube a cube in the ground field. The determinant then has 21st power
one, hence is a cube in the cyclic group of order 63. The unitary equation
makes its cube root have norm one; scaling by its inverse gives an actual
special-unitary representative, contradicting outerness.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.8, printed p.1188, the paragraph beginning with the case `n = 3`.
This proves the linear PGU calculation used there; the full automorphism
centralizer assembly is in `UnitaryEight.Reduction`.
-/

open Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UnitaryEight
variable {E : Type*} [Field E]

private theorem cube_root_of_pow_twentyone [Finite E] (hcard : Nat.card E = 64)
    (a : Eˣ) (ha : a^21 = 1) : ∃ d : Eˣ, d^3 = a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr (hg a) : ∃ n : ℕ, g^n = a)
  change g^n = a at hn
  have hord : orderOf g = 63 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  have hdiv : 63 ∣ n * 21 := by
    rw [← hord, orderOf_dvd_iff_pow_eq_one, pow_mul, hn]
    exact ha
  have hn3 : 3 ∣ n := by omega
  obtain ⟨k, rfl⟩ := hn3
  exact ⟨g^k, by rw [← pow_mul, Nat.mul_comm k 3, hn]⟩

private theorem projective_pow_scalar (A : GL (Fin 3) E) (n : ℕ)
    (h : (ProjGenLinGroup.mk A)^n = 1) :
    ∃ a : Eˣ, A^n = GeneralLinearGroup.scalar (Fin 3) a := by
  have hc : A^n ∈ Subgroup.center (GL (Fin 3) E) :=
    ProjGenLinGroup.mk_eq_one.mp (by simpa only [map_pow] using h)
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨a, ha⟩ := hc
  exact ⟨a, ha.symm⟩

private theorem trace_sq [CharP E 2] (A : Matrix (Fin 3) (Fin 3) E) :
    (A^2).trace = A.trace^2 := by
  simp only [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]
  ring_nf
  simp [CharTwo.two_eq_zero]

private theorem projective_involution_trace_ne_zero [CharP E 2]
    (A : GL (Fin 3) E) (h : (ProjGenLinGroup.mk A)^2 = 1) : A.val.trace ≠ 0 := by
  obtain ⟨a, ha⟩ := projective_pow_scalar A 2 h
  have ht := congrArg (fun B : GL (Fin 3) E => B.val.trace) ha
  change (A.val^2).trace = (Matrix.scalar (Fin 3) (a : E)).trace at ht
  rw [trace_sq] at ht
  have h3 : (3 : E) = 1 := by
    calc (3 : E) = 2 + 1 := by norm_num
         _ = 1 := by rw [CharTwo.two_eq_zero, zero_add]
  have ht' : A.val.trace^2 = (a : E) := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_three, h3] using ht
  intro hz
  rw [hz, zero_pow (by decide)] at ht'
  exact a.ne_zero ht'.symm

private theorem commute_of_projective_involution [CharP E 2]
    (A B : GL (Fin 3) E) (hB : (ProjGenLinGroup.mk B)^2 = 1)
    (h : Commute (ProjGenLinGroup.mk A) (ProjGenLinGroup.mk B)) : Commute A B := by
  have htrace := projective_involution_trace_ne_zero B hB
  have hp : ProjGenLinGroup.mk (A * B * A⁻¹) = ProjGenLinGroup.mk B := by
    simpa only [map_mul, map_inv] using (mul_inv_eq_iff_eq_mul).mpr h.eq
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have ht := congrArg (fun X : GL (Fin 3) E => X.val.trace) hc
  have hm : ((A * B * A⁻¹) * GeneralLinearGroup.scalar (Fin 3) c).val =
      (c : E) • (A.val * B.val * (A⁻¹).val) := by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal, mul_comm]
  rw [hm, trace_smul, trace_units_conj] at ht
  have hc1 : c = 1 := Units.ext (mul_right_cancel₀ htrace (ht.trans (one_mul _).symm))
  rw [hc1, map_one, mul_one] at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc : A * B = B * A)

private theorem mem_psu_of_scalar_cube [Finite E]
    (J : HermitianForm 3 E) (hcard : Nat.card E = 64)
    (hfixed : Nat.card {z : E // J.conj z = z} = 8)
    (u : J.unitarySubgroup) (a : Eˣ)
    (hu : u.val^3 = GeneralLinearGroup.scalar (Fin 3) (a^3)) :
    ProjGenLinGroup.mk u.val ∈ ProjectiveSpecialUnitaryMatrixGroup J := by
  have units_pow (x : Eˣ) : x^63 = 1 := by
    have h := pow_card_eq_one' (x := x)
    rwa [Nat.card_units, hcard] at h
  have hd : (GeneralLinearGroup.det u.val)^3 = a^9 := by
    have h := congrArg GeneralLinearGroup.det hu
    simpa only [map_pow, GeneralLinearGroup.det_scalar, Fintype.card_fin, ← pow_mul] using h
  have hd21 : (GeneralLinearGroup.det u.val)^21 = 1 := by
    calc
      _ = ((GeneralLinearGroup.det u.val)^3)^7 := (pow_mul _ 3 7)
      _ = (a^9)^7 := by rw [hd]
      _ = 1 := by simpa only [← pow_mul] using units_pow a
  obtain ⟨d, hd⟩ := cube_root_of_pow_twentyone hcard (GeneralLinearGroup.det u.val) hd21
  have hconj := BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J 8
    (by simpa using hcard) hfixed
  have hu9 : (GeneralLinearGroup.det u.val)^9 = 1 := by
    apply Units.ext
    change u.val.val.det^9 = 1
    have h := J.unitary_det_norm_one u
    rw [hconj] at h
    simpa only [pow_succ] using h
  have hd27 : d^27 = 1 := by simpa only [← hd, ← pow_mul] using hu9
  have hd9 : d^9 = 1 := by
    have h := units_pow d
    rw [show (63 : ℕ) = 27 + 27 + 9 from rfl, pow_add, pow_add, hd27, one_mul] at h
    simpa only [one_mul] using h
  have hdnorm : J.conj (d : E) * (d : E) = 1 := by
    rw [hconj]
    have h : (d : E)^9 = 1 := congrArg (fun x : Eˣ => (x : E)) hd9
    simpa only [pow_succ] using h
  have hinorm : J.conj ((d⁻¹ : Eˣ) : E) * ((d⁻¹ : Eˣ) : E) = 1 := by
    simp only [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hdnorm, inv_one]
  let w : J.specialSubgroup :=
    ⟨GeneralLinearGroup.scalar (Fin 3) d⁻¹ * u.val,
      J.unitarySubgroup.mul_mem (J.scalar_mem_unitary_of_norm_one d⁻¹ hinorm) u.property,
      by
        change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) d⁻¹ * u.val) = 1
        simp [map_mul, GeneralLinearGroup.det_scalar, ← hd]⟩
  have hw : ProjGenLinGroup.mk w.val = ProjGenLinGroup.mk u.val := by
    simp [w, map_mul]
  rw [← hw]
  simpa only [J.specialToProjective_apply_val] using (J.specialToProjective w).property

private theorem eigenvector_of_commute_square_zero
    (A N : Module.End E (Fin 3 → E)) (hN : N ≠ 0)
    (hsq : N * N = 0) (hcomm : Commute A N) :
    ∃ (a : E) (w : Fin 3 → E), w ≠ 0 ∧ A w = a • w := by
  have hle : LinearMap.range N ≤ LinearMap.ker N :=
    LinearMap.range_le_ker_iff.mpr hsq
  have hrank := LinearMap.finrank_range_add_finrank_ker N
  have hmono := Submodule.finrank_mono hle
  have hpos : Module.finrank E (LinearMap.range N) ≠ 0 := by
    intro h
    exact hN (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h))
  have hdim : Module.finrank E (LinearMap.range N) = 1 := by
    rw [Module.finrank_fin_fun] at hrank
    omega
  have hbot : LinearMap.range N ≠ ⊥ := by
    intro h
    exact hN (LinearMap.range_eq_bot.mp h)
  obtain ⟨w, hw, hw0⟩ := (LinearMap.range N).ne_bot_iff.mp hbot
  have haw : A w ∈ LinearMap.range N := by
    obtain ⟨y, rfl⟩ := hw
    refine ⟨A y, ?_⟩
    exact (congrArg (fun f : Module.End E (Fin 3 → E) => f y) hcomm.eq).symm
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hdim
    (x := (⟨w, hw⟩ : LinearMap.range N)) (by simpa using hw0)
    (⟨A w, haw⟩ : LinearMap.range N)
  exact ⟨a, w, hw0, (congrArg Subtype.val ha).symm⟩

private theorem eigenvector_of_projective_involution [CharP E 2]
    (A B : GL (Fin 3) E) (hB : (ProjGenLinGroup.mk B)^2 = 1)
    (hB0 : ProjGenLinGroup.mk B ≠ 1) (hcomm : Commute A B) :
    ∃ (a : E) (w : Fin 3 → E), w ≠ 0 ∧ A.val *ᵥ w = a • w := by
  obtain ⟨b, hb⟩ := projective_pow_scalar B 2 hB
  have ht := congrArg (fun X : GL (Fin 3) E => X.val.trace) hb
  change (B.val^2).trace = (Matrix.scalar (Fin 3) (b : E)).trace at ht
  have h3 : (3 : E) = 1 := by
    calc (3 : E) = 2 + 1 := by norm_num
         _ = 1 := by rw [CharTwo.two_eq_zero, zero_add]
  have ht' : B.val.trace^2 = (b : E) := by
    rw [trace_sq] at ht
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_three, h3] using ht
  have hscalar (c : E) : Matrix.scalar (Fin 3) c = c • (1 : Matrix (Fin 3) (Fin 3) E) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hsq : B.val^2 = B.val.trace^2 • (1 : Matrix (Fin 3) (Fin 3) E) := by
    rw [ht', ← hscalar]
    exact congrArg Units.val hb
  let U : Module.End E (Fin 3 → E) := A.val.toLin'
  let V : Module.End E (Fin 3 → E) := B.val.toLin'
  let N := V - B.val.trace • (1 : Module.End E (Fin 3 → E))
  have hV : V^2 = B.val.trace^2 • (1 : Module.End E (Fin 3 → E)) := by
    simpa only [Matrix.toLin'_pow, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
      using congrArg Matrix.toLin' hsq
  have hN : N ≠ 0 := by
    intro hz
    have hv : V = B.val.trace • (1 : Module.End E (Fin 3 → E)) := sub_eq_zero.mp hz
    have hm : B.val = Matrix.scalar (Fin 3) B.val.trace := by
      apply Matrix.toLin'.injective
      rw [hscalar, map_smul, Matrix.toLin'_one]
      exact hv
    apply hB0
    exact ProjGenLinGroup.mk_eq_one.mpr
      (GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨_, hm.symm⟩)
  have hN2 : N * N = 0 := by
    dsimp [N]
    rw [sub_mul, mul_sub, mul_sub]
    simp only [mul_smul_comm, smul_mul_assoc, one_mul, mul_one, smul_smul]
    rw [← pow_two V, ← pow_two B.val.trace, hV]
    have hdup (f : Module.End E (Fin 3 → E)) : f + f = 0 := by
      apply LinearMap.ext
      intro w
      funext i
      exact CharTwo.add_self_eq_zero (f w i)
    calc
      _ = (B.val.trace^2 • (1 : Module.End E (Fin 3 → E)) + B.val.trace^2 • 1) -
          (B.val.trace • V + B.val.trace • V) := by abel
      _ = 0 := by rw [hdup, hdup, sub_self]
  have hUV : Commute U V := by
    have h := congrArg (fun X : GL (Fin 3) E => X.val.toLin') hcomm.eq
    change U * V = V * U
    simpa only [Units.val_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
  have hUN : Commute U N := by
    show U * (V - B.val.trace • 1) = (V - B.val.trace • 1) * U
    rw [mul_sub, sub_mul, hUV.eq, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  exact eigenvector_of_commute_square_zero U N hN hN2 hUN

private theorem mem_psu_of_eigenvector [Finite E]
    (J : HermitianForm 3 E) (hcard : Nat.card E = 64)
    (hfixed : Nat.card {z : E // J.conj z = z} = 8)
    (u : J.unitarySubgroup) (hu : (ProjGenLinGroup.mk u.val)^3 = 1)
    (a : E) (w : Fin 3 → E) (hw0 : w ≠ 0) (hw : u.val.val *ᵥ w = a • w) :
    ProjGenLinGroup.mk u.val ∈ ProjectiveSpecialUnitaryMatrixGroup J := by
  obtain ⟨c, hc⟩ := projective_pow_scalar u.val 3 hu
  have hp : (u.val.val^3) *ᵥ w = a^3 • w := by
    calc
      _ = u.val.val *ᵥ (u.val.val *ᵥ (u.val.val *ᵥ w)) := by
        simp only [pow_succ, pow_zero, one_mul, mulVec_mulVec, mul_assoc]
      _ = a^3 • w := by
        simp only [hw, mulVec_smul, smul_smul]
        congr 1
        ring
  have he : (c : E) = a^3 := by
    apply smul_left_injective E hw0
    have hmat : u.val.val^3 = Matrix.scalar (Fin 3) (c : E) := congrArg Units.val hc
    rw [hmat] at hp
    simpa [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_def, smul_eq_mul] using hp
  have ha0 : a ≠ 0 := by
    intro ha
    subst a
    simp only [zero_pow (by decide : (3 : ℕ) ≠ 0)] at he
    exact c.ne_zero he
  let a' : Eˣ := Units.mk0 a ha0
  apply mem_psu_of_scalar_cube J hcard hfixed u a'
  rw [hc]
  congr 1
  exact Units.ext he

/-- An outer projective cubic in the actual unitary group over the field of
order 64 has no nonidentity commuting projective involution. -/
public theorem linearCentralizerBound [Finite E]
    (J : HermitianForm 3 E) (hcard : Nat.card E = 64)
    (hfixed : Nat.card {z : E // J.conj z = z} = 8) : LinearCentralizerBound J := by
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := 6) (by
    simpa only [← Nat.card_eq_fintype_card, show (2 : ℕ)^6 = 64 from rfl] using hcard)
  intro u v hu houter hv hcomm
  by_contra hv0
  have hc : Commute u.val v.val := commute_of_projective_involution u.val v.val hv hcomm.symm
  obtain ⟨a, w, hw0, hw⟩ := eigenvector_of_projective_involution u.val v.val hv hv0 hc
  exact houter (mem_psu_of_eigenvector J hcard hfixed u hu a w hw0 hw)

end BenderSuzuki.MatrixGroups.HermitianForm.UnitaryEight
