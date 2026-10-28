module

public import Theory.SpecificGroups.SL3.InvolutionDerived
public import Theory.SpecificGroups.SL2.PrimeToResidual
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.SpecificGroups.SU3.InvolutionConjugacy
public import Theory.SpecificGroups.SU3.UnitaryTwoResidual
public import ABG.ChapterII.Section2.SpecialUnitaryEquivSL2
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Basic

/-!
# Involution conjugacy and centralizer residuals in SL₃(p) and SU₃(p)

For each odd prime p, both actual matrix groups have one class of involutions.
Every involution centralizer is GL₂(p), respectively GU₂(p); its prime-to-p
residual is genuinely isomorphic to SL₂(ZMod p) and contains the terminal
derived subgroup. The unitary model has matrix field GF(p²), identity Gram
matrix, and conjugation x ↦ x^p. All field and form witnesses are discharged.
These assertions include p = 3: the residual calculation uses transvection
generation, not perfectness.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.3.21(a), printed p. 55 (PDF p. 66).
-/

public section

namespace CFSG.Quasithin.ChapterA.Section03

private theorem oddPrime_two_ne_zero (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (2 : ZMod p) ≠ 0 := by
  apply CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two
  obtain ⟨k, hk⟩ := hp
  omega

/-- The determinant-one block subgroup in the standard linear involution centralizer. -/
@[expose] noncomputable def sl3_standard_detKernel (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    Subgroup (Matrix.SL3.standardCentralizer (ZMod p)) :=
  (Matrix.SL3.centralizerDet (ZMod p) (by exact oddPrime_two_ne_zero p hp)).ker

/-- The block determinant kernel is the actual SL₂ over the prime field. -/
noncomputable def sl3_standard_detKernel_equiv (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    sl3_standard_detKernel p hp ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  Matrix.SL3.centralizerDetKernelEquiv (ZMod p) (oddPrime_two_ne_zero p hp)

/-- The terminal derived subgroup of the linear centralizer lies in this SL₂. -/
theorem sl3_standard_terminalDerived_le_detKernel (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (⨅ n : ℕ, derivedSeries (Matrix.SL3.standardCentralizer (ZMod p)) n) ≤
      sl3_standard_detKernel p hp :=
  Matrix.SL3.centralizer_terminalDerived_le_detKernel (ZMod p) (oddPrime_two_ne_zero p hp)

/-- The prime-to-p residual of the linear centralizer lies in the determinant kernel. -/
theorem sl3_standard_primeToResidual_le_detKernel (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    Subgroup.primeToResidual p (Matrix.SL3.standardCentralizer (ZMod p)) ≤
      sl3_standard_detKernel p hp := by
  apply Subgroup.primeToResidual_le_ker
  rw [Nat.card_eq_fintype_card, ZMod.card_units]
  exact (Nat.coprime_self_sub_right (Fact.out : p.Prime).one_lt.le).mpr (Nat.coprime_one_right p)

/-- The standard linear involution centralizer has determinant kernel O^{p′}. -/
theorem sl3_standard_primeToResidual_eq_detKernel (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    Subgroup.primeToResidual p (Matrix.SL3.standardCentralizer (ZMod p)) =
      sl3_standard_detKernel p hp := by
  apply le_antisymm (sl3_standard_primeToResidual_le_detKernel p hp)
  intro x hx
  let e := Matrix.SL3.standardInvolutionCentralizerEquiv (ZMod p)
    (oddPrime_two_ne_zero p hp)
  have hx' : e.symm x ∈ (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod p)).ker := by
    simpa only [sl3_standard_detKernel, MonoidHom.mem_ker,
      Matrix.SL3.centralizerDet_apply] using hx
  have hm : e.symm x ∈ Subgroup.primeToResidual p (GL (Fin 2) (ZMod p)) := by
    rw [Matrix.GeneralLinearGroup.primeToResidual_eq_det_ker]
    exact hx'
  have hmap : x ∈ (Subgroup.primeToResidual p (GL (Fin 2) (ZMod p))).map
      e.toMonoidHom := ⟨e.symm x, hm, e.apply_symm_apply x⟩
  rwa [Subgroup.map_primeToResidual e] at hmap

/-- The prime-to-p residual of the standard involution centralizer is SL₂(p). -/
noncomputable def sl3_standard_primeToResidual_equiv (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    Subgroup.primeToResidual p (Matrix.SL3.standardCentralizer (ZMod p)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  (MulEquiv.subgroupCongr (sl3_standard_primeToResidual_eq_detKernel p hp)).trans
    (sl3_standard_detKernel_equiv p hp)

/-- The terminal derived subgroup lies in O^{p′} for the standard linear centralizer. -/
theorem sl3_standard_terminalDerived_le_primeToResidual (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (⨅ n : ℕ, derivedSeries (Matrix.SL3.standardCentralizer (ZMod p)) n) ≤
      Subgroup.primeToResidual p (Matrix.SL3.standardCentralizer (ZMod p)) := by
  rw [sl3_standard_primeToResidual_eq_detKernel]
  exact sl3_standard_terminalDerived_le_detKernel p hp

private theorem commutator_le_residual_of_equiv {G H : Type*} [Group G] [Group H]
    (p : ℕ) (e : G ≃* H)
    (h : commutator H ≤ Subgroup.primeToResidual p H) :
    commutator G ≤ Subgroup.primeToResidual p G := by
  intro x hx
  have he : e x ∈ commutator H :=
    (map_derivedSeries_le_derivedSeries e.toMonoidHom 1) ⟨x, hx, rfl⟩
  have hm : x ∈ (Subgroup.primeToResidual p H).map e.symm.toMonoidHom :=
    ⟨e x, h he, e.symm_apply_apply x⟩
  rwa [Subgroup.map_primeToResidual] at hm

/-- All involutions in the actual SL₃(p) are conjugate. -/
theorem sl3_involutions_isConj (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (z w : Matrix.SpecialLinearGroup (Fin 3) (ZMod p))
    (hz : orderOf z = 2) (hw : orderOf w = 2) : IsConj z w :=
  Matrix.SL3.involutions_isConj (ZMod p) z w hz hw (oddPrime_two_ne_zero p hp)

/-- The full centralizer of every SL₃(p) involution is GL₂(p). -/
noncomputable def sl3_involutionCentralizerEquiv (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (z : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) (hz : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) ≃*
      GL (Fin 2) (ZMod p) :=
  Matrix.SL3.involutionCentralizerEquiv (ZMod p) z hz (oddPrime_two_ne_zero p hp)

/-- For every involution, O^{p′}(C_SL₃(p)(z)) is the actual SL₂(p). -/
noncomputable def sl3_involution_primeToResidual_equiv
    (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (z : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) (hz : orderOf z = 2) :
    Subgroup.primeToResidual p
      (Subgroup.centralizer ({z} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  (Subgroup.primeToResidualEquiv p (sl3_involutionCentralizerEquiv p hp z hz)).trans
    ((MulEquiv.subgroupCongr (Matrix.GeneralLinearGroup.primeToResidual_eq_det_ker p)).trans
      (Matrix.SpecialLinearGroup.determinantKernelEquiv (Fin 2) (ZMod p)).symm)

/-- The terminal derived subgroup of every linear involution centralizer lies in O^{p′}. -/
theorem sl3_involution_terminalDerived_le_primeToResidual
    (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (z : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) (hz : orderOf z = 2) :
    (⨅ n : ℕ, derivedSeries
      (Subgroup.centralizer ({z} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))) n) ≤
    Subgroup.primeToResidual p
      (Subgroup.centralizer ({z} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))) := by
  apply (iInf_le _ 1).trans
  apply commutator_le_residual_of_equiv p (sl3_involutionCentralizerEquiv p hp z hz)
  rw [Matrix.GeneralLinearGroup.primeToResidual_eq_det_ker]
  exact Abelianization.commutator_subset_ker _

/-- The actual identity-Gram SU₃(p), over its quadratic representation field. -/
noncomputable abbrev RankThreeSU (p : ℕ) [Fact p.Prime] :=
  (ABG.unitaryForm 3 p 1 (by decide)).specialSubgroup

private theorem oddPrime_ne_two (p : ℕ) (hp : Odd p) : p ≠ 2 := by
  obtain ⟨k, hk⟩ := hp
  omega

private theorem unitaryForm_prime_conj (m p : ℕ) [Fact p.Prime]
    (x : GaloisField p (2 * 1)) :
    (ABG.unitaryForm m p 1 (by decide)).conj x = x ^ p := by
  simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]

private theorem quadratic_units_coprime (p : ℕ) [Fact p.Prime] :
    Nat.Coprime p (Nat.card (GaloisField p (2 * 1))ˣ) := by
  rw [Nat.card_units, GaloisField.card p (2 * 1) (by decide)]
  apply (Nat.coprime_pow_left_iff (by decide : 0 < 2) p (p ^ 2 - 1)).mp
  exact (Nat.coprime_self_sub_right (by
    have hp := (Fact.out : p.Prime).one_lt
    nlinarith)).mpr (Nat.coprime_one_right (p ^ 2))

/-- SU₂ for the standard quadratic field is genuinely SL₂ over ZMod p. -/
noncomputable def su2_prime_equiv_sl2 (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (ABG.unitaryForm 2 p 1 (by decide)).specialSubgroup ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  (ABG.specialUnitaryTwo_equiv_sl2 p 1 hp (by decide)).trans
    (GorensteinWalter.sl2RingEquiv (GaloisField.equivZmodP p).toRingEquiv)

/-- O^{p′}(GU₂(p)) equals the determinant kernel, including p = 3. -/
theorem gu2_primeToResidual_eq_detKernel (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    Subgroup.primeToResidual p (ABG.GU2 p 1 (by decide)) =
      (ABG.unitaryForm 2 p 1 (by decide)).unitaryDet.ker :=
  (ABG.unitaryForm 2 p 1 (by decide)).primeToResidual_eq_unitaryDet_ker p
    (su2_prime_equiv_sl2 p hp) (quadratic_units_coprime p)

/-- All involutions in the actual SU₃(p) are conjugate inside SU₃(p). -/
theorem su3_involutions_isConj (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (z w : RankThreeSU p) (hz : orderOf z = 2) (hw : orderOf w = 2) : IsConj z w :=
  Matrix.SU3.involutions_isConj (oddPrime_ne_two p hp)
    (GaloisField.card p (2 * 1) (by decide))
    (ABG.unitaryForm 3 p 1 (by decide)) rfl (unitaryForm_prime_conj 3 p) z w hz hw

/-- The full centralizer of every SU₃(p) involution is the actual GU₂(p). -/
noncomputable def su3_involutionCentralizerEquiv (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (z : RankThreeSU p) (hz : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set (RankThreeSU p)) ≃* ABG.GU2 p 1 (by decide) :=
  (Matrix.SU3.involutionCentralizerEquiv (oddPrime_ne_two p hp)
    (GaloisField.card p (2 * 1) (by decide))
    (ABG.unitaryForm 3 p 1 (by decide)) (ABG.unitaryForm 2 p 1 (by decide))
    rfl rfl (unitaryForm_prime_conj 3 p) (unitaryForm_prime_conj 2 p) z hz).symm

/-- For every involution, O^{p′}(C_SU₃(p)(z)) is the actual SL₂(p). -/
noncomputable def su3_involution_primeToResidual_equiv
    (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (z : RankThreeSU p) (hz : orderOf z = 2) :
    Subgroup.primeToResidual p (Subgroup.centralizer ({z} : Set (RankThreeSU p))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  (Subgroup.primeToResidualEquiv p (su3_involutionCentralizerEquiv p hp z hz)).trans
    ((ABG.unitaryForm 2 p 1 (by decide)).unitaryPrimeToResidualEquiv p
      (su2_prime_equiv_sl2 p hp) (quadratic_units_coprime p))

/-- The terminal derived subgroup of every unitary involution centralizer lies in O^{p′}. -/
theorem su3_involution_terminalDerived_le_primeToResidual
    (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (z : RankThreeSU p) (hz : orderOf z = 2) :
    (⨅ n : ℕ, derivedSeries (Subgroup.centralizer ({z} : Set (RankThreeSU p))) n) ≤
      Subgroup.primeToResidual p (Subgroup.centralizer ({z} : Set (RankThreeSU p))) :=
  (iInf_le _ 1).trans (commutator_le_residual_of_equiv p
    (su3_involutionCentralizerEquiv p hp z hz)
    ((ABG.unitaryForm 2 p 1 (by decide)).unitary_commutator_le_primeToResidual p
      (su2_prime_equiv_sl2 p hp) (quadratic_units_coprime p)))

/-- A.3.21(a) for the actual SL₃(p): one nonempty involution class, with
SL₂(p) prime-to-p centralizer residual containing the terminal derived subgroup. -/
theorem sl3_involution_structure (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    ∃ z : Matrix.SpecialLinearGroup (Fin 3) (ZMod p), orderOf z = 2 ∧
      ∀ w : Matrix.SpecialLinearGroup (Fin 3) (ZMod p), orderOf w = 2 →
        IsConj z w ∧
        Nonempty (Subgroup.primeToResidual p
          (Subgroup.centralizer ({w} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))) ≃*
            Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ∧
        (⨅ n : ℕ, derivedSeries
          (Subgroup.centralizer ({w} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))) n) ≤
          Subgroup.primeToResidual p
            (Subgroup.centralizer ({w} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))) := by
  let z := Matrix.SL3.standardInvolution (ZMod p)
  have hz : orderOf z = 2 := Matrix.SL3.standardInvolution_orderOf (ZMod p)
    (oddPrime_two_ne_zero p hp)
  exact ⟨z, hz, fun w hw => ⟨sl3_involutions_isConj p hp z w hz hw,
    ⟨sl3_involution_primeToResidual_equiv p hp w hw⟩,
    sl3_involution_terminalDerived_le_primeToResidual p hp w hw⟩⟩

/-- A.3.21(a) for the actual SU₃(p) over GF(p²), with Frobenius conjugation:
one nonempty involution class and the claimed SL₂(p) centralizer residual. -/
theorem su3_involution_structure (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    ∃ z : RankThreeSU p, orderOf z = 2 ∧
      ∀ w : RankThreeSU p, orderOf w = 2 → IsConj z w ∧
        Nonempty (Subgroup.primeToResidual p
          (Subgroup.centralizer ({w} : Set (RankThreeSU p))) ≃*
            Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ∧
        (⨅ n : ℕ, derivedSeries (Subgroup.centralizer ({w} : Set (RankThreeSU p))) n) ≤
          Subgroup.primeToResidual p (Subgroup.centralizer ({w} : Set (RankThreeSU p))) := by
  let z : RankThreeSU p := Matrix.SU3.standardInvolution
    (ABG.unitaryForm 3 p 1 (by decide)) rfl
  have hz : orderOf z = 2 := Matrix.SU3.standardInvolution_orderOf
    (ABG.unitaryForm 3 p 1 (by decide)) rfl
    (CharP.cast_ne_zero_of_ne_of_prime (GaloisField p (2 * 1)) Nat.prime_two
      (oddPrime_ne_two p hp))
  exact ⟨z, hz, fun w hw => ⟨su3_involutions_isConj p hp z w hz hw,
    ⟨su3_involution_primeToResidual_equiv p hp w hw⟩,
    su3_involution_terminalDerived_le_primeToResidual p hp w hw⟩⟩

end CFSG.Quasithin.ChapterA.Section03

end
