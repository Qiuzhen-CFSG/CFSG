module

public import Theory.SpecificGroups.SU3.GraphFixedFixer
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Coverage

/-!
# Automorphisms centralizing the graph-fixed subgroup and graph involution

The corner-unipotent calculation underlying `GraphFixedFixer` forces a
semilinear pointwise fixer to have diagonal unitary part with equal corner
entries, and field part either identity or Hermitian conjugation. The local
coordinate lemmas are retained here because the earlier module exposes only
the two-part bound. Hermitian conjugation inverts this diagonal action.
Commutation with it makes the diagonal action involutory; its odd order
then makes it trivial. Semilinear coverage is discharged from the two field
cardinalities, so both conditions on an arbitrary automorphism suffice.

Source: GLS4, Chapter 4, Lemma 3.4(d1); the trace-one calculation follows
`Theory/SpecificGroups/SU3/GraphFixedFixer.lean`.
-/

open Matrix MulAction
namespace BenderSuzuki.MatrixGroups.HermitianForm.FixedRigidity
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

omit [CharP E 2] in
private theorem graph_inverts_diagonal (u : J.unitarySubgroup)
    (hshape : u.val.val = !![u.val.val 0 0, 0, 0; 0, u.val.val 1 1, 0; 0, 0, u.val.val 0 0]) :
    projectiveGraphAut J hJ * J.unitaryConj u * projectiveGraphAut J hJ =
      (J.unitaryConj u)⁻¹ := by
  have hu := (J.mem_unitarySubgroup_iff _).mp u.property
  rw [hshape, hJ] at hu
  have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2) hu
  have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 1) hu
  simp [HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_three] at h0 h1
  have hi : GeneralLinearGroup.map J.conj.toRingHom u.val = u.val⁻¹ := by
    apply mul_eq_one_iff_eq_inv.mp
    apply Units.ext
    change u.val.val.map J.conj * u.val.val = 1
    rw [hshape]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1]
  have hγ := projectiveGraphAut_isEntrywiseConjugation J hJ
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change (projectiveGraphAut J hJ (J.unitaryConj u (projectiveGraphAut J hJ x))).val = _
  rw [hγ.apply_val, J.unitaryConj_apply_val, map_mul, map_mul, map_inv,
    ProjGenLinGroup.map_mk, hi]
  have hinv : (J.unitaryConj u)⁻¹ = J.unitaryConj u⁻¹ := by
    symm
    apply eq_inv_iff_mul_eq_one.mpr
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    change (J.unitaryConj u⁻¹ (J.unitaryConj u y)).val = y.val
    simp [J.unitaryConj_apply_val, mul_assoc]
  rw [hinv, J.unitaryConj_apply_val]
  have hh : projectiveGraphAut J hJ (projectiveGraphAut J hJ x) = x := by
    obtain ⟨v, rfl⟩ := J.specialToProjective_surjective x
    rw [projectiveGraphAut_specialToProjective, projectiveGraphAut_specialToProjective,
      specialGraphAut_involutive]
  have hh' := congrArg Subtype.val hh
  rw [hγ.apply_val] at hh'
  rw [hh']
  rfl

/-- Both pointwise fixation and centralization of the graph involution force
an automorphism to be identity or that graph involution. -/
public theorem graph_fixedCentralizer [Finite E] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hcomm : Commute b (projectiveGraphAut J hJ))
    (hfix : ∀ x, projectiveGraphAut J hJ x = x → b x = x) :
    b = 1 ∨ b = projectiveGraphAut J hJ := by
  let γ := projectiveGraphAut J hJ
  have hγ2 : γ * γ = 1 := by
    apply MulEquiv.ext
    intro x
    change projectiveGraphAut J hJ (projectiveGraphAut J hJ x) = x
    obtain ⟨v, rfl⟩ := J.specialToProjective_surjective x
    rw [projectiveGraphAut_specialToProjective, projectiveGraphAut_specialToProjective,
      specialGraphAut_involutive]
  have hb : b ∈ fixingSubgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
      ((projectiveGraphAut J hJ).fixedSubgroup : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    intro x
    exact hfix x ((MulAut.mem_fixedSubgroup _ _).mp x.property)
  obtain ⟨σ, u, hu⟩ := J.semilinear_coverage n hn hJ hcard hfixed b
  obtain ⟨hshape, hσ⟩ := constraints J hJ b hb σ u hu
  have hpure (c : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
      (hc : c = J.unitaryConj u) (hcfix : ∀ x, γ x = x → c x = x)
      (hccomm : Commute c γ) : c = 1 := by
    have hinv : γ * c * γ = c⁻¹ := by
      rw [hc]
      exact graph_inverts_diagonal J hJ u hshape
    have hcsq : c ^ 2 = 1 := by
      have heq : c = c⁻¹ := by
        calc c = c * (γ * γ) := by rw [hγ2, mul_one]
             _ = γ * c * γ := by rw [← mul_assoc, hccomm.eq]
             _ = c⁻¹ := hinv
      simpa only [pow_two] using (mul_eq_one_iff_eq_inv.mpr heq)
    have hcfix' : c ∈ fixingSubgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
        ((projectiveGraphAut J hJ).fixedSubgroup : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      intro x
      exact hcfix x ((MulAut.mem_fixedSubgroup _ _).mp x.property)
    have hp := identity_field_pow J hJ c hcfix'
      ((HasUnitarySemilinearForm.one_iff J).mpr ⟨u, hc⟩)
    have hodd : Odd (Nat.card E - 1) := by
      rw [hcard]
      exact Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (by positivity))
        ((even_two.pow_of_ne_zero (show n ≠ 0 by omega)).pow_of_ne_zero (by decide)) odd_one
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hodd.coprime_two_left
      (orderOf_dvd_of_pow_eq_one hcsq) (orderOf_dvd_of_pow_eq_one hp))
  rcases field_cases J hn hcard hfixed σ hσ with hσ1 | hσc
  · have hbu : b = J.unitaryConj u := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [hu, hσ1, J.unitaryConj_apply_val]
      change _ * ProjGenLinGroup.map (RingHom.id E) x.val * _ = _
      rw [ProjGenLinGroup.map_id, MonoidHom.id_apply]
    exact Or.inl (hpure b hbu hfix hcomm)
  · have hbu : b = J.unitaryConj u * γ := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      change (b x).val = (J.unitaryConj u (γ x)).val
      rw [hu, hσc, J.unitaryConj_apply_val,
        (projectiveGraphAut_isEntrywiseConjugation J hJ).apply_val]
    have hcfix : ∀ x, γ x = x → J.unitaryConj u x = x := by
      intro x hx
      have hbfix := hfix x hx
      rw [hbu] at hbfix
      change J.unitaryConj u (γ x) = x at hbfix
      rwa [hx] at hbfix
    have hccomm : Commute (J.unitaryConj u) γ := by
      change J.unitaryConj u * γ = γ * J.unitaryConj u
      apply mul_right_cancel (b := γ)
      simpa only [hbu, mul_assoc] using hcomm.eq
    have hc1 := hpure (J.unitaryConj u) rfl hcfix hccomm
    exact Or.inr (by rw [hbu, hc1, one_mul])

end BenderSuzuki.MatrixGroups.HermitianForm.FixedRigidity
