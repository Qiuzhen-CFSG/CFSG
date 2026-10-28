module

public import Theory.GroupTheory.CubicProductQuotient
public import Theory.SpecificGroups.ClassicalOrthogonal.RankOneComparison.Comparison
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus
public import Theory.SpecificGroups.ProjectiveLinearThree

/-!
# Cubic witnesses and the orthogonal scalar kernels

The companion matrix of `X² + X + 1` gives an element of order three in SL₂
over every field, including characteristic three. The actual rank-one odd
Omega carrier also contains such an element, by its proved conjugation-model
comparison with PSL₂. Thus the smallest complementary dimension in A.2.17
does not require a simplicity assumption.

For both Siegel-generated and commutator Omega carriers, scalar kernel
elements have square one. Consequently any embedded product of SL₂ and a
group containing a cubic element retains an elementary subgroup of order nine
after the literal orthogonal projectivization.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, A.2.17, printed p.39. These are the scalar and rank
steps; fundamental-subgroup embeddings and their centralizers are not assumed
proved by this module.
-/

public noncomputable section

open Matrix
namespace ClassicalOrthogonal.Fundamental
universe u
variable {F : Type u} [Field F]

/-- A fixed companion matrix of order three, in all characteristics. -/
@[expose] def cubicSL : SpecialLinearGroup (Fin 2) F :=
  ⟨!![-1, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- The companion matrix has cube one. -/
theorem cubicSL_cube : (cubicSL (F := F)) ^ 3 = 1 := by
  apply Subtype.ext
  change (cubicSL (F := F)).val ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicSL, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The off-diagonal entry one makes the companion matrix nonidentity. -/
theorem cubicSL_order : orderOf (cubicSL (F := F)) = 3 := by
  apply orderOf_eq_prime cubicSL_cube
  intro h
  have h10 := congrArg (fun g : SpecialLinearGroup (Fin 2) F => g.val 1 0) h
  simp [cubicSL] at h10

/-- The actual ternary Omega carrier contains a cubic element, even over F₃. -/
theorem oddRankOne_exists_cubic : ∃ x : OmegaOdd 1 F, orderOf x = 3 := by
  obtain ⟨x, hx⟩ := Matrix.ProjectiveSpecialLinearGroup.exists_orderOf_eq_three F 2 le_rfl
  let e := RankOneComparison.elementaryEquivPSL (F := F)
  refine ⟨e.symm x, ?_⟩
  exact (orderOf_injective e.symm.toMonoidHom e.symm.injective x).trans hx

variable {V : Type u} [AddCommGroup V] [Module F V]

/-- Scalars in the elementary orthogonal carrier have square one. -/
theorem elementaryScalar_square (Q : QuadraticForm F V)
    (g : elementarySubgroup Q) (hg : g ∈ elementaryScalarSubgroup Q) : g ^ 2 = 1 := by
  obtain ⟨c, hc, hg⟩ := hg
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change g.val.val (g.val.val v) = v
  rw [hg, hg, smul_smul, ← pow_two, hc, one_smul]

/-- An embedded group inherits a square-one kernel under projectivization. -/
theorem elementaryProjective_kernel_square (Q : QuadraticForm F V)
    {A : Type*} [Group A] (f : A →* elementarySubgroup Q) (hf : Function.Injective f)
    (x : A) (hx : projectiveElementaryMap Q (f x) = 1) : x ^ 2 = 1 := by
  apply hf
  rw [map_pow, map_one]
  exact elementaryScalar_square Q (f x)
    ((projectiveElementaryMap_eq_one_iff Q (f x)).mp hx)

/-- On the commutator carrier, a nonzero quadratic value forces scalar square one. -/
theorem omegaScalar_square (Q : QuadraticForm F V) (hQ : ∃ v, Q v ≠ 0)
    (g : Minus.Omega F V Q) (hg : g ∈ Minus.scalarSubgroup F V Q) : g ^ 2 = 1 := by
  obtain ⟨c, hg⟩ := hg
  obtain ⟨v, hv⟩ := hQ
  have hc : (c : F) ^ 2 = 1 := by
    have h := (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup Q g.val.val).mp
      g.val.property v
    rw [hg] at h
    apply mul_right_cancel₀ hv
    simpa only [Q.map_smul, smul_eq_mul, pow_two, one_mul] using h
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  change g.val.val (g.val.val w) = w
  rw [hg, hg, smul_smul, ← pow_two, hc, one_smul]

/-- The same kernel bound for the literal commutator/scalar quotient. -/
theorem omegaProjective_kernel_square (Q : QuadraticForm F V) (hQ : ∃ v, Q v ≠ 0)
    {A : Type*} [Group A] (f : A →* Minus.Omega F V Q) (hf : Function.Injective f)
    (x : A) (hx : QuotientGroup.mk' (Minus.scalarSubgroup F V Q) (f x) = 1) :
    x ^ 2 = 1 := by
  apply hf
  rw [map_pow, map_one]
  exact omegaScalar_square Q hQ (f x) ((QuotientGroup.eq_one_iff _).mp hx)

/-- Two cubic factors survive the projectivization of an elementary carrier. -/
theorem elementaryProjective_contains_nine {H : Type*} [Group H]
    (Q : QuadraticForm F V)
    (f : SpecialLinearGroup (Fin 2) F × H →* elementarySubgroup Q)
    (hf : Function.Injective f) (h : H) (hh : orderOf h = 3) :
    ∃ E : Subgroup (ProjectiveElementary Q),
      E ≤ ((projectiveElementaryMap Q).comp f).range ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  exact CubicProductQuotient.exists_nine ((projectiveElementaryMap Q).comp f)
    (elementaryProjective_kernel_square Q f hf) cubicSL h cubicSL_order hh

/-- Two cubic factors survive the projectivization used by the minus carrier. -/
theorem omegaProjective_contains_nine {H : Type*} [Group H]
    (Q : QuadraticForm F V) (hQ : ∃ v, Q v ≠ 0)
    (f : SpecialLinearGroup (Fin 2) F × H →* Minus.Omega F V Q)
    (hf : Function.Injective f) (h : H) (hh : orderOf h = 3) :
    ∃ E : Subgroup (Minus.ProjectiveOmega F V Q),
      E ≤ ((QuotientGroup.mk' (Minus.scalarSubgroup F V Q)).comp f).range ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  exact CubicProductQuotient.exists_nine ((QuotientGroup.mk' (Minus.scalarSubgroup F V Q)).comp f)
    (omegaProjective_kernel_square Q hQ f hf) cubicSL h cubicSL_order hh

/-- Every square-kernel quotient of SL₂ × Ω₃ contains an elementary subgroup
of order nine. This verifies the rank step for the dimension-seven factors,
without presupposing their realization as a centralizer. -/
theorem sevenModel_contains_nine
    (N : Subgroup (SpecialLinearGroup (Fin 2) F × OmegaOdd 1 F)) [N.Normal]
    (hN : ∀ x ∈ N, x ^ 2 = 1) :
    ∃ E : Subgroup ((SpecialLinearGroup (Fin 2) F × OmegaOdd 1 F) ⧸ N),
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨b, hb⟩ := oddRankOne_exists_cubic (F := F)
  obtain ⟨E, _, hE, hc⟩ := CubicProductQuotient.exists_nine (QuotientGroup.mk' N)
    (fun x hx => hN x ((QuotientGroup.eq_one_iff _).mp hx)) cubicSL b cubicSL_order hb
  exact ⟨E, hE, hc⟩

end ClassicalOrthogonal.Fundamental
