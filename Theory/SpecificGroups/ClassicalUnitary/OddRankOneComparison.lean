module

public import Theory.SpecificGroups.ClassicalUnitary.TheoremDRootNormalizer.BinaryForms

/-!
# The actual odd-field PSU₂–PSL₂ comparison

For any finite Hermitian coefficient field of order q² with conjugation x ↦ x^q,
the fixed field has order q. An orthonormal basis, a norm-minus-one element,
and a nonzero anti-fixed element give the existing SU₂–SL₂ equivalence.
Transport of central elements through its explicit inverse identifies the
kernel of the projection into PGL with the whole center of SU₂. Passing to
these literal quotients proves PSU₂(q) ≃ PSL₂(q), for every odd prime power.

The comparison is uniform in the stored Hermitian form. It does not infer a
projective equivalence from an abstract special-group equivalence alone.

Sources: Huppert, *Endliche Gruppen I*, II.10.4, and Alperin–Brauer–Gorenstein,
II.2 Lemma 1(vi), article p.17, for the underlying two-dimensional comparison.
The consumer `Classical.OddLinearUnitary` uses it for the dimension-two unitary
aliases in Aschbacher–Smith B.1.13, printed pp.73–74.
-/

public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open HermitianForm.IdentityGram
open Theory.SpecificGroups.UnitaryRootNormalizer
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {F : Type*} [Field F] [Finite F]

/-- The stored q-Frobenius has exactly q fixed elements. -/
theorem fixed_card_prime_power {d q : ℕ} (J : HermitianForm d F)
    (hq : IsPrimePow q) (hc : Nat.card F = q ^ 2)
    (hj : ∀ x, J.conj x = x ^ q) :
    Nat.card {x : F // J.conj x = x} = q := by
  obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  let : Fact p.Prime := ⟨hp⟩
  let K := GaloisField p (2 * a)
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = (p ^ a) ^ 2 := by
    rw [GaloisField.card p (2 * a) (by omega), ← pow_mul, Nat.mul_comm a 2]
  let e : F ≃+* K := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hc.trans hK.symm)
  let σ := iterateFrobeniusEquiv K p a
  have he (x : F) : J.conj x = x ↔ σ (e x) = e x := by
    rw [hj, iterateFrobeniusEquiv_def, ← map_pow]
    exact e.injective.eq_iff.symm
  exact (Nat.card_congr (e.toEquiv.subtypeEquiv he)).trans
    (GaloisField.card_fixedBy_quadraticFrobenius p a (by omega))

private theorem nonempty_skew_basis_odd (J : HermitianForm 2 F) {q : ℕ}
    (hq : IsPrimePow q) (ho : Odd q) (hc : Nat.card F = q ^ 2)
    (hj : ∀ x, J.conj x = x ^ q) :
    ∃ (C : GL (Fin 2) F) (s : F), s ≠ 0 ∧
      (identityGram J).conjTranspose C.val * (identityGram J).form * C.val =
        s • !![0, 1; -1, 0] := by
  let I := identityGram J
  have hk := J.fixed_card_prime_power hq hc hj
  have h2 : (2 : F) ≠ 0 := by
    intro h
    let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h
    let : Fintype F := Fintype.ofFinite F
    have hh := FiniteField.even_card_of_char_two (ringChar.eq F 2)
    rw [← Nat.card_eq_fintype_card, hc] at hh
    have hh' := Nat.not_even_iff_odd.mpr (ho.pow : Odd (q ^ 2))
    exact hh' (even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero hh))
  obtain ⟨z, _, hz⟩ := External.huppert_II_10_4_norm_surjective I q hc hk
    (-1) (by simp) (by simp)
  have hex : ∃ a : F, I.conj a ≠ a := by
    by_contra! hall
    let e : {x : F // J.conj x = x} ≃ F :=
      { toFun := Subtype.val
        invFun := fun a => ⟨a, hall a⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have he := Nat.card_congr e
    rw [hk, hc] at he
    have hq1 : 1 < q := hq.one_lt
    nlinarith
  obtain ⟨a, ha⟩ := hex
  have ht0 : a - I.conj a ≠ 0 := sub_ne_zero.mpr ha.symm
  have ht : I.conj (a - I.conj a) = -(a - I.conj a) := by
    rw [map_sub, I.conj_involutive a]
    ring
  obtain ⟨C, _, hC⟩ := exists_skew_basis I rfl h2 z (a - I.conj a) hz ht0 ht
  exact ⟨C, 2 * (a - I.conj a), mul_ne_zero h2 ht0, hC⟩

omit [Finite F] in
private theorem projectTwo_ker_eq_center_of_skew
    (J : HermitianForm 2 F) (C : GL (Fin 2) F) (s : F) (hs : s ≠ 0)
    (hC : J.conjTranspose C.val * J.form * C.val = s • !![0, 1; -1, 0]) :
    (projectTwo J).ker = Subgroup.center J.specialSubgroup := by
  let K := FixedBy.subfield F J.conj
  let e := J.specialUnitaryEquivFixed C s hs hC
  apply le_antisymm
  · intro A hA
    have hz : A.val ∈ Subgroup.center (GL (Fin 2) F) :=
      Matrix.ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val hA)
    exact Subgroup.mem_center_iff.mpr fun B =>
      Subtype.ext (Subgroup.mem_center_iff.mp hz B.val)
  · intro A hA
    have he : e A ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) :=
      (Subgroup.centerCongr e ⟨A, hA⟩).property
    obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp he
    let B := SpecialLinearGroup.toGL (SpecialLinearGroup.map K.subtype (e A))
    have hB : B.val = Matrix.scalar (Fin 2) (r : F) := by
      change (fun i j => ((e A).val i j : F)) = _
      rw [← hr]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    have hb : B ∈ Subgroup.center (GL (Fin 2) F) := by
      apply Subgroup.mem_center_iff.mpr
      intro D
      apply Units.ext
      change D.val * B.val = B.val * D.val
      rw [hB]
      exact (Matrix.scalar_commute (r : F) (Commute.all _) D.val).symm
    have hAeq : A.val = C * B * C⁻¹ := by
      have hh := J.specialUnitaryEquivFixed_symm_apply_val C s hs hC (e A)
      change (e.symm (e A)).val = C * B * C⁻¹ at hh
      simpa only [e.symm_apply_apply] using hh
    have ha : A.val ∈ Subgroup.center (GL (Fin 2) F) := by
      rw [hAeq, Subgroup.mem_center_iff.mp hb C, mul_inv_cancel_right]
      exact hb
    apply Subtype.ext
    exact Matrix.ProjGenLinGroup.mk_eq_one.mpr ha

/-- Every actual odd-field PSU₂ model is PSL₂ over its actual fixed field. -/
theorem nonempty_projectiveTwoEquiv_odd (J : HermitianForm 2 F) {q : ℕ}
    (hq : IsPrimePow q) (ho : Odd q) (hc : Nat.card F = q ^ 2)
    (hj : ∀ x, J.conj x = x ^ q) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃*
      ProjectiveSpecialLinearGroup (Fin 2) (FixedBy.subfield F J.conj)) := by
  have hk := J.fixed_card_prime_power hq hc hj
  obtain ⟨C, hC⟩ := External.huppert_II_10_4_a_orthonormal_basis 2 J q hc hk
  let I := identityGram J
  obtain ⟨D, s, hs, hD⟩ := nonempty_skew_basis_odd J hq ho hc hj
  let e := I.specialUnitaryEquivFixed D s hs hD
  have hker := projectTwo_ker_eq_center_of_skew I D s hs hD
  let ep := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (projectTwo I) (projectTwo_surjective I))
  have he : (Subgroup.center I.specialSubgroup).map e.toMonoidHom =
      Subgroup.center (SpecialLinearGroup (Fin 2) (FixedBy.subfield F J.conj)) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (Subgroup.centerCongr e ⟨a, ha⟩).property
    · intro hx
      exact ⟨e.symm x, ((Subgroup.centerCongr e).symm ⟨x, hx⟩).property,
        e.apply_symm_apply x⟩
  exact ⟨((projectiveEquiv J C hC).trans ep.symm).trans
    (QuotientGroup.congr _ _ e he)⟩

end BenderSuzuki.MatrixGroups.HermitianForm
