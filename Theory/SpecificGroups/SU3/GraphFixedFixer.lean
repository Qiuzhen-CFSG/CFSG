module

public import Theory.SpecificGroups.SU3.GraphFixedResidual
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Semilinear
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.GroupTheory.Sylow

/-!
# The full automorphism fixer of the binary unitary graph-fixed subgroup

Assuming the concrete unitary-semilinear coverage theorem, the pointwise fixer
of the actual graph-fixed subgroup of PSU₃(q) has order not divisible by four.
The same holds for its embedded two-residual when q = 2ⁿ and n ≥ 2. Both the
matrix-field order q² and the fixed-field order q are retained.

The trace-one upper and lower corner unipotents remove projective scalar
ambiguity and force the conjugating matrix to be diagonal with equal corner
entries. Varying the fixed-field parameter then forces the field part to fix
that field pointwise, so it is identity or Hermitian conjugation. The
identity-field part has exponent dividing |E| - 1, which is odd. In a putative
subgroup of order four it is therefore trivial; multiplication of semilinear
formulas then makes every two nonidentity elements equal, a contradiction.
This argument allows odd-order elements in the full fixer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
16.1.4(6) and the centralizer argument in 16.4.9(1), printed pp.1171 and 1189
of the 1 March 2004 combined manuscript. Semilinear coverage is an explicit
input, owned by the separate automorphism-classification development.
-/

open Matrix MulAction
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E]

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

variable (J : HermitianForm 3 E) [CharP E 2]
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

private def upper (t : E) (ht : J.conj t = t) : J.specialSubgroup := by
  let X : Matrix (Fin 3) (Fin 3) E := !![1, 0, t; 0, 1, 0; 0, 0, 1]
  refine ⟨GeneralLinearGroup.mkOfDetNeZero X (by simp [X, det_fin_three]), ?_⟩
  rw [J.mem_specialSubgroup_iff]
  constructor
  · rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
        ht, CharTwo.add_self_eq_zero]
  · apply Units.ext
    change X.det = 1
    simp [X, det_fin_three]

private def lower : J.specialSubgroup := by
  let X : Matrix (Fin 3) (Fin 3) E := !![1, 0, 0; 0, 1, 0; 1, 0, 1]
  refine ⟨GeneralLinearGroup.mkOfDetNeZero X (by simp [X, det_fin_three]), ?_⟩
  rw [J.mem_specialSubgroup_iff]
  constructor
  · rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
        CharTwo.add_self_eq_zero]
  · apply Units.ext
    change X.det = 1
    simp [X, det_fin_three]

private theorem upper_fixed (t : E) (ht : J.conj t = t) :
    J.specialToProjective (upper J hJ t ht) ∈ (projectiveGraphAut J hJ).fixedSubgroup := by
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  rw [projectiveGraphAut_specialToProjective]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [specialGraphAut_apply_val]
  ext i j
  change J.conj ((upper J hJ t ht).val.val i j) = (upper J hJ t ht).val.val i j
  fin_cases i <;> fin_cases j <;> simp [upper, ht]

private theorem lower_fixed :
    J.specialToProjective (lower J hJ) ∈ (projectiveGraphAut J hJ).fixedSubgroup := by
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  rw [projectiveGraphAut_specialToProjective]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [specialGraphAut_apply_val]
  ext i j
  change J.conj ((lower J hJ).val.val i j) = (lower J hJ).val.val i j
  fin_cases i <;> fin_cases j <;> simp [lower]

private theorem constraints
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ∈ fixingSubgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
      ((projectiveGraphAut J hJ).fixedSubgroup : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    (σ : E ≃+* E) (u : J.unitarySubgroup)
    (hu : ∀ b : ProjectiveSpecialUnitaryMatrixGroup J,
      (a b).val = ProjGenLinGroup.mk u.val * ProjGenLinGroup.map σ.toRingHom b.val *
        (ProjGenLinGroup.mk u.val)⁻¹) :
    u.val.val = !![u.val.val 0 0, 0, 0; 0, u.val.val 1 1, 0; 0, 0, u.val.val 0 0] ∧
      ∀ t : E, J.conj t = t → σ t = t := by
  have hc (X : J.specialSubgroup)
      (hfix : J.specialToProjective X ∈ (projectiveGraphAut J hJ).fixedSubgroup)
      (htr : X.val.val.trace = 1) :
      u.val.val * X.val.val.map σ = X.val.val * u.val.val := by
    apply untwist u.val X.val (GeneralLinearGroup.map σ.toRingHom X.val) htr
    · change (X.val.val.map σ).trace = 1
      rw [← AddMonoidHom.map_trace, htr, map_one]
    · have hh := hu (J.specialToProjective X)
      rw [show a (J.specialToProjective X) = J.specialToProjective X from ha ⟨_, hfix⟩,
        J.specialToProjective_apply_val, ProjGenLinGroup.map_mk] at hh
      simpa only [map_mul, map_inv] using hh.symm
  have hU := hc (upper J hJ 1 (map_one _)) (upper_fixed J hJ 1 (map_one _)) (by
    simp [upper, Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero])
  have hL := hc (lower J hJ) (lower_fixed J hJ) (by
    simp [lower, Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero])
  have hUmap : (upper J hJ 1 (map_one _)).val.val.map σ =
      !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper]
  have hLmap : (lower J hJ).val.val.map σ = !![1, 0, 0; 0, 1, 0; 1, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lower]
  rw [hUmap] at hU
  rw [hLmap] at hL
  change u.val.val * !![1, 0, 1; 0, 1, 0; 0, 0, 1] =
    !![1, 0, 1; 0, 1, 0; 0, 0, 1] * u.val.val at hU
  change u.val.val * !![1, 0, 0; 0, 1, 0; 1, 0, 1] =
    !![1, 0, 0; 0, 1, 0; 1, 0, 1] * u.val.val at hL
  have h20 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 0) hU
  have h21 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) hU
  have hdiag := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2) hU
  have h10 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 2) hU
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 2) hL
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 1) hL
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 0) hL
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h20 h21 hdiag h10 h02 h01 h12
  have hdg : u.val.val 0 0 = u.val.val 2 2 := by simpa [h02] using hdiag
  have hshape : u.val.val =
      !![u.val.val 0 0, 0, 0; 0, u.val.val 1 1, 0; 0, 0, u.val.val 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h20, h21, hdg, h10, h02, h01, h12]
  refine ⟨hshape, ?_⟩
  have h00 : u.val.val 0 0 ≠ 0 := by
    have hd := u.val.det_ne_zero
    rw [hshape] at hd
    intro hh
    simp [Matrix.det_fin_three, hh] at hd
  intro t ht
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2)
    (hc (upper J hJ t ht) (upper_fixed J hJ t ht) (by
      simp [upper, Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero]))
  simp [upper, Matrix.mul_apply, Fin.sum_univ_three, h02, ← hdg] at h
  exact mul_left_cancel₀ h00 (by simpa [mul_comm] using h)

omit [CharP E 2] in
private theorem field_cases [Finite E] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (σ : E ≃+* E) (hσ : ∀ t : E, J.conj t = t → σ t = t) :
    σ = 1 ∨ σ = J.conj := by
  classical
  let K := FixedBy.subfield E J.conj
  let s : E ≃ₐ[K] E := AlgEquiv.ofRingEquiv (f := σ) (fun x => hσ x x.property)
  let c : E ≃ₐ[K] E := AlgEquiv.ofRingEquiv (f := J.conj) (fun x => x.property)
  have hdegree : Module.finrank K E = 2 := by
    have hh := Module.natCard_eq_pow_finrank (K := K) (V := E)
    change Nat.card E = Nat.card {x : E // J.conj x = x} ^ Module.finrank K E at hh
    rw [hcard, hfixed] at hh
    exact (pow_right_inj₀ (by positivity : 0 < 2 ^ n)
      (Nat.one_lt_two_pow (show n ≠ 0 by omega)).ne').mp hh.symm
  have hle : Nat.card (E ≃ₐ[K] E) ≤ 2 := by
    rw [← hdegree, Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  have hc : c ≠ 1 := by
    intro hh
    apply conj_ne_one_of_card J n hn hcard hfixed
    ext x
    exact congrArg (fun f : E ≃ₐ[K] E => f x) hh
  have hs : s = 1 ∨ s = c := by
    by_contra! hh
    have hsub : ({1, s, c} : Finset (E ≃ₐ[K] E)) ⊆ Finset.univ := Finset.subset_univ _
    have h := (Finset.card_le_card hsub).trans (by
      simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using hle)
    simp [hh.2, Ne.symm hh.1, Ne.symm hc] at h
  rcases hs with hs | hs
  · exact Or.inl (RingEquiv.ext fun x => congrArg (fun f : E ≃ₐ[K] E => f x) hs)
  · exact Or.inr (RingEquiv.ext fun x => congrArg (fun f : E ≃ₐ[K] E => f x) hs)

private theorem identity_field_pow [Finite E]
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ∈ fixingSubgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
      ((projectiveGraphAut J hJ).fixedSubgroup : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hf : J.HasUnitarySemilinearForm a 1) : a ^ (Nat.card E - 1) = 1 := by
  classical
  obtain ⟨u, hu⟩ := hf
  have hshape := (constraints J hJ a ha 1 u hu).1
  have hdiag : u.val.val = Matrix.diagonal (fun i => u.val.val i i) := by
    rw [hshape]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hne (i : Fin 3) : u.val.val i i ≠ 0 := by
    have hd := u.val.det_ne_zero
    rw [hdiag, Matrix.det_diagonal] at hd
    exact (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ i)
  have hupow : u ^ (Nat.card E - 1) = 1 := by
    apply Subtype.ext
    apply Units.ext
    change u.val.val ^ (Nat.card E - 1) = (1 : Matrix (Fin 3) (Fin 3) E)
    conv_lhs => rw [hdiag, Matrix.diagonal_pow]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    change u.val.val i i ^ (Nat.card E - 1) = 1
    let := Fintype.ofFinite E
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card_sub_one_eq_one _ (hne i)
  let f : J.unitarySubgroup →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) := {
    toFun := J.unitaryConj
    map_one' := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      simp [J.unitaryConj_apply_val]
    map_mul' := by
      intro u v
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      simp [J.unitaryConj_apply_val, mul_assoc] }
  have haf : a = f u := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [hu]
    change _ * ProjGenLinGroup.map (RingHom.id E) b.val * _ = _
    rw [ProjGenLinGroup.map_id, MonoidHom.id_apply]
    exact (J.unitaryConj_apply_val u b).symm
  rw [haf, ← map_pow, hupow, map_one]

/-- The full automorphism fixer of the embedded graph-fixed subgroup has
no subgroup of order four, conditional on concrete semilinear coverage. -/
public theorem graph_fixed_fixer_not_four_dvd [Finite E] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (hcover : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
      ((projectiveGraphAut J hJ).fixedSubgroup : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  classical
  let B := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite B := Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Finite (MulAut B) := Finite.of_injective (fun a : MulAut B => (a : B → B))
    DFunLike.coe_injective
  let F := fixingSubgroup (MulAut B) ((projectiveGraphAut J hJ).fixedSubgroup : Set B)
  have hforms (a : F) : J.HasUnitarySemilinearForm a.val 1 ∨
      J.HasUnitarySemilinearForm a.val J.conj := by
    obtain ⟨σ, u, hu⟩ := hcover a.val
    have hf := (constraints J hJ a.val a.property σ u hu).2
    rcases field_cases J hn hcard hfixed σ hf with rfl | rfl
    · exact Or.inl ⟨u, hu⟩
    · exact Or.inr ⟨u, hu⟩
  have hodd : Odd (Nat.card E - 1) := by
    rw [hcard]
    exact Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (by positivity))
      ((even_two.pow_of_ne_zero (show n ≠ 0 by omega)).pow_of_ne_zero (by decide)) odd_one
  have hcop : Nat.Coprime 4 (Nat.card E - 1) := hodd.coprime_two_left.pow_left 2
  have hconj : J.conj * J.conj = 1 := by
    ext x
    exact J.conj_involutive x
  intro hfour
  obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) 2 (n := 2)
    (by simpa only [show 2 ^ 2 = 4 from rfl] using hfour)
  norm_num at hV
  have hpure (a : V) (ha : J.HasUnitarySemilinearForm a.val.val 1) : a = 1 := by
    have hpow : a.val.val ^ 4 = 1 := by
      have hh := congrArg (fun z : V => z.val.val) (pow_card_eq_one' (x := a))
      simpa only [hV, Subgroup.coe_pow, OneMemClass.coe_one] using hh
    have hd := identity_field_pow J hJ a.val.val a.val.property ha
    have ho : orderOf a.val.val = 1 := Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one hd)
    exact Subtype.ext (Subtype.ext (orderOf_eq_one_iff.mp ho))
  have hsame (x y : V) (hx : J.HasUnitarySemilinearForm x.val.val J.conj)
      (hy : J.HasUnitarySemilinearForm y.val.val J.conj) : x * y = 1 := by
    apply hpure
    simpa only [hconj, Subgroup.coe_mul] using hx.mul J hJ hy
  let f : V → Bool := fun a => decide (a ≠ 1)
  have hinj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = 1 <;> by_cases hy : y = 1
    · exact hx.trans hy.symm
    · simp [f, hx, hy] at hxy
    · simp [f, hx, hy] at hxy
    · have hxf := (hforms x.val).resolve_left (fun h => hx (hpure x h))
      have hyf := (hforms y.val).resolve_left (fun h => hy (hpure y h))
      exact mul_right_cancel ((hsame x y hxf hyf).trans (hsame y y hyf hyf).symm)
  have hh := Nat.card_le_card_of_injective f hinj
  norm_num [hV, Nat.card_eq_fintype_card] at hh

/-- The same bound for the two-residual inside the original projective group;
no abstract replacement of its embedding is made. -/
public theorem graph_embeddedFixedResidual_fixer_not_four_dvd [Finite E]
    {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (hcover : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
      (MulAut.embeddedFixedResidual 2 (projectiveGraphAut J hJ) :
        Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  rw [graph_embeddedFixedResidual_eq_fixed J hJ hn hfixed]
  exact graph_fixed_fixer_not_four_dvd J hJ hn hcard hfixed hcover

end BenderSuzuki.MatrixGroups.HermitianForm
