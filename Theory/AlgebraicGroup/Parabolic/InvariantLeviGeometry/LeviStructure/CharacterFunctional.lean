module
public import Theory.AlgebraicGroup.Parabolic.InvariantLeviGeometry.RootTransport

/-!
# An integral functional separating the standard Levi roots

Use the integral simple-root basis supplied by the actual root datum and sum
its coordinates outside J.  Transport along the character-lattice isomorphism
gives an integral character functional.  Positive-root coefficients are
nonnegative, and vanishing outside J is exactly membership in the Levi root
subsystem, so the functional is positive on the unipotent roots and zero on
the Levi roots.  The argument also covers the empty complement of J.

Source: GLS3, 1.13.1 and 1.13.4; Borel, IV, 14.17--14.18.
-/

namespace Theory.AlgebraicGroup.InvariantLeviGeometry
open scoped BigOperators
universe u
variable {k : Type u} [Field k] {K : Variety k} [AlgebraicGroup K]
  (S : StandardParabolicRelativeRootSetup K)

private theorem integral_root_coord (a j : S.ι) (hj : j ∈ S.integralBase.support) :
    S.integralBase.toWeightBasis.repr (S.integralPairing.root a) ⟨j, hj⟩ =
      S.coeff a j := by
  classical
  let := Fintype.ofFinite S.ι
  have hrepr := congrArg S.integralBase.toWeightBasis.repr
    (S.integralSimpleRootExpansion a).1
  simp only [map_sum, map_smul] at hrepr
  have h := congrArg (fun v : S.integralBase.support →₀ ℤ => v ⟨j, hj⟩) hrepr
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply] at h
  have hcoord (i : S.ι) (hi : i ∈ S.integralBase.support) :
      S.integralBase.toWeightBasis.repr (S.integralPairing.root i) ⟨j, hj⟩ =
        if i = j then 1 else 0 := by
    simpa [Finsupp.single_apply] using congrArg
      (fun v : S.integralBase.support →₀ ℤ => v ⟨j, hj⟩)
      (S.integralBase.toWeightBasis_repr_root ⟨i, hi⟩)
  have hs : (∑ i ∈ S.integralBase.support, S.coeff a i •
      S.integralBase.toWeightBasis.repr (S.integralPairing.root i) ⟨j, hj⟩) =
      S.coeff a j := by
    rw [Finset.sum_eq_single_of_mem j hj]
    · simp [hcoord j hj]
    · intro i hi hij
      simp [hcoord i hi, hij]
  exact h.trans hs

private theorem coeff_nonneg_of_positive {a : S.D.Root} (ha : a ∈ S.positiveRoots)
    (j : S.ι) (hj : j ∈ S.integralBase.support) : 0 ≤ S.coeff (S.rootEquiv a) j := by
  classical
  let := Fintype.ofFinite S.ι
  obtain ⟨f, _, hfSign, hfRoot⟩ := S.integralBase.exists_root_eq_sum_int (S.rootEquiv a)
  have hpos : 0 < f := by
    apply hfSign.resolve_right
    intro hneg
    have hapos := (S.actualRootDatum.2.2 a).mp ha
    rw [RootPairing.Base.isPos_iff, RootPairing.Base.height_eq_sum hfRoot] at hapos
    exact (not_lt_of_ge (Finset.sum_nonpos (fun i _ => hneg.le i))) hapos
  have hc : S.coeff (S.rootEquiv a) j = f j := by
    rw [← integral_root_coord S _ j hj, hfRoot]
    simp only [map_sum, map_zsmul]
    have hcoord (i : S.ι) (hi : i ∈ S.integralBase.support) :
        S.integralBase.toWeightBasis.repr (S.integralPairing.root i) ⟨j, hj⟩ =
          if i = j then 1 else 0 := by
      simpa [Finsupp.single_apply] using congrArg
        (fun v : S.integralBase.support →₀ ℤ => v ⟨j, hj⟩)
        (S.integralBase.toWeightBasis_repr_root ⟨i, hi⟩)
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply]
    rw [Finset.sum_eq_single_of_mem j hj]
    · simp [hcoord j hj]
    · intro i hi hij
      simp [hcoord i hi, hij]
  rw [hc]
  exact hpos.le j

/-- The actual integral root datum supplies a functional that vanishes on
Levi roots and is strictly positive on the standard unipotent roots. -/
public theorem exists_levi_separating_characterFunctional :
    ∃ phi : Additive (TorusWeight S.T) →+ ℤ,
      (∀ a ∈ S.positiveRoots \ S.sigmaJ,
        0 < phi (Additive.ofMul (S.D.rootWeight a))) ∧
      (∀ a ∈ S.sigmaJ, phi (Additive.ofMul (S.D.rootWeight a)) = 0) := by
  classical
  let := Fintype.ofFinite S.ι
  let b := S.integralBase.toWeightBasis
  let w : S.integralBase.support → ℤ :=
    fun i => if S.rootEquiv.symm i.val ∈ S.J then 0 else 1
  let f : S.X →ₗ[ℤ] ℤ := b.constr ℤ w
  let e : S.X ≃+ Additive (TorusWeight S.T) :=
    (AddEquiv.additiveMultiplicative S.X).symm.trans S.weightEquiv.toAdditive
  let phi : Additive (TorusWeight S.T) →+ ℤ :=
    f.toAddMonoidHom.comp e.symm.toAddMonoidHom
  have hphi (a : S.D.Root) : phi (Additive.ofMul (S.D.rootWeight a)) =
      ∑ j : S.integralBase.support, S.coeff (S.rootEquiv a) j * w j := by
    have hweight : e.symm (Additive.ofMul (S.D.rootWeight a)) =
        S.integralPairing.root (S.rootEquiv a) := by
      apply e.injective
      rw [e.apply_symm_apply]
      change Additive.ofMul (S.D.rootWeight a) =
        Additive.ofMul (S.weightEquiv (Multiplicative.ofAdd (S.integralPairing.root (S.rootEquiv a))))
      rw [S.actualRootDatum.2.1 a]
    change f (e.symm (Additive.ofMul (S.D.rootWeight a))) = _
    rw [hweight]
    change (b.constr ℤ w) (S.integralPairing.root (S.rootEquiv a)) = _
    rw [Module.Basis.constr_apply_fintype]
    simp only [Module.Basis.equivFun_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_root_coord S _ j j.property]
    rfl
  refine ⟨phi, ?_, ?_⟩
  · intro a ha
    rw [hphi]
    have hn : ∀ j : S.integralBase.support, 0 ≤ S.coeff (S.rootEquiv a) j * w j := by
      intro j
      exact mul_nonneg (coeff_nonneg_of_positive S ha.1 j j.property)
        (by dsimp [w]; split_ifs <;> norm_num)
    have hex : ∃ j ∈ S.integralBase.support,
        S.rootEquiv.symm j ∉ S.J ∧ S.coeff (S.rootEquiv a) j ≠ 0 := by
      by_contra! h
      apply ha.2
      apply (mem_sigma_iff_coeff_zero S a).mpr
      intro j hj hjJ
      have hj' : j ∈ S.integralBase.support := by rwa [S.baseSupport_eq] at hj
      exact h j hj' hjJ
    obtain ⟨j, hj, hjJ, hjne⟩ := hex
    apply Finset.sum_pos' (fun j _ => hn j)
    refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
    dsimp [w]
    rw [if_neg hjJ, mul_one]
    exact lt_of_le_of_ne (coeff_nonneg_of_positive S ha.1 j hj) (Ne.symm hjne)
  · intro a ha
    rw [hphi]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hjJ : S.rootEquiv.symm j.val ∈ S.J
    · simp [w, hjJ]
    · have hzero := (mem_sigma_iff_coeff_zero S a).mp ha j
        (by rw [S.baseSupport_eq]; exact j.property) hjJ
      rw [hzero, zero_mul]
end Theory.AlgebraicGroup.InvariantLeviGeometry
