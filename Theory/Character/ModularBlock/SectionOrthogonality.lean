module

public import Theory.Character.ModularBlock.MixedBrauerTrace
public import Theory.Character.ModularBlock.BrauerCoefficientExtension
public import Theory.GroupTheory.PrimeRegularDecomposition
public import Theory.Representation.IntegralTwistedPermutationTrace

/-!
# Principal-block kernel support on two-sections

The column kernel of the ordinary principal two-block, based at a two-element
`u`, vanishes outside the two-section of `u`. Decompose the other group element
as `t * v`, where `t` has two-power order and `v` has odd order and commutes
with `t`. Outside the section, `u` and `t` are not conjugate. Thus the
left-right permutation for `u,t` has two-power order and no fixed basis
vectors. It commutes with the odd-order right permutation for `v` and with
the actual integral principal-block projector. The twisted integral trace
theorem makes their product trace zero. Mapping to the complex numbers
identifies this trace with the character-column pairing.

The original two-element case is retained below. Neither statement requires
a decomposition matrix or an integral realization of an individual
irreducible character.
Source: Brauer, *Some applications of the theory of blocks of characters
of finite groups II* (1964), §IV, Proposition 4, pp.312–313; the trace
realization is the Brauer--Suzuki permutation-summand argument.
-/

public section
noncomputable section

open scoped BigOperators
namespace ModularBlock.SectionOrthogonality
open PrincipalBlockConstruction BrauerBlockReduction BrauerConjugationTrace
open MixedBrauerTrace MixedConjugationTrace BlockOrthogonality
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- Distinct conjugacy classes of two-elements have orthogonal principal-block columns. -/
theorem principalBlock_column_eq_zero_of_not_isConj
    (d : PrincipalCongruenceBlockData G) (u w : G)
    (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1) (hw : ∃ n : ℕ, w ^ (2 ^ n) = 1)
    (hne : ¬ IsConj u w) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk u) *
      star (d.chi i (ConjClasses.mk w)) = 0 := by
  classical
  let R := Localization.AtPrime d.primeIdeal
  let : Field (principalResidueField d) := Ideal.Quotient.field d.primeIdeal
  let σ := leftRightPerm u w
  let e := localizedPrincipalBlockElement d
  obtain ⟨n, hn⟩ := hu
  obtain ⟨m, hm⟩ := hw
  have hσ : σ ^ (2 ^ (n + m)) = 1 := by
    apply leftRightPerm_pow_eq_one
    · rw [pow_add, pow_mul, hn, one_pow]
    · rw [Nat.add_comm n m, pow_add, pow_mul, hm, one_pow]
  have hfix (x : G) : σ x ≠ x := by
    intro h
    apply hne
    apply isConj_iff.mpr
    refine ⟨x⁻¹, ?_⟩
    change u⁻¹ * x * w = x at h
    calc
      x⁻¹ * u * (x⁻¹)⁻¹ = x⁻¹ * u * (u⁻¹ * x * w) := by rw [h, inv_inv]
      _ = w := by group
  let F := {x // σ x = x}
  let : IsEmpty F := ⟨fun x => hfix x.val x.property⟩
  have hsurj : Function.Surjective (localizationToResidue d) := by
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨algebraMap _ R a, localizationToResidue_algebraMap d a⟩
  have hf (r : R) (hr : localizationToResidue d r ≠ 0) : IsUnit r := by
    by_contra hn
    exact hr ((BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit d r).mpr hn)
  have ht := Matrix.trace_permMatrix_mul_eq_trace_fixed_lift
    (localizationToResidue d) hsurj hf σ hσ (rightMatrix e)
    (rightMatrix_isIdempotent e (localizedPrincipalBlockElement_isIdempotent d))
    (rightMatrix_commute_leftRight e (localizedPrincipalBlockElement_mem_center d) u w)
    (0 : Matrix F F R) (by simp [IsIdempotentElem]) (by ext x; exact isEmptyElim x)
  have htrace : LinearMap.trace R (MonoidAlgebra R G) (projectedLeftRight e u w) = 0 := by
    rw [MixedBrauerTrace.trace_permMatrix_mul_rightMatrix] at ht
    simpa only [Matrix.trace_zero] using ht
  have hc := congrArg (IsotypicLattice.localizationToComplex d) htrace
  rw [trace_projectedLeftRight, map_sum, map_zero] at hc
  rw [← principalBlock_leftRight_trace,
    ← mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement d
      (IsotypicLattice.localizationToComplex d) (IsotypicLattice.localizationToComplex_algebraMap d),
    trace_projectedLeftRight]
  exact hc

private theorem principalBlock_column_eq_zero_of_not_isConj_twoPart
    (d : PrincipalCongruenceBlockData G) (u t v : G)
    (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1) (ht : ∃ n : ℕ, t ^ (2 ^ n) = 1)
    (hv : Odd (orderOf v)) (htv : Commute t v) (hne : ¬ IsConj u t) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk u) *
      star (d.chi i (ConjClasses.mk (t * v))) = 0 := by
  classical
  let R := Localization.AtPrime d.primeIdeal
  let : Field (principalResidueField d) := Ideal.Quotient.field d.primeIdeal
  let σ := leftRightPerm u t
  let τ := leftRightPerm 1 v
  let e := localizedPrincipalBlockElement d
  obtain ⟨n, hn⟩ := hu
  obtain ⟨l, hl⟩ := ht
  have hσ : σ ^ (2 ^ (n + l)) = 1 := by
    apply leftRightPerm_pow_eq_one
    · rw [pow_add, pow_mul, hn, one_pow]
    · rw [Nat.add_comm n l, pow_add, pow_mul, hl, one_pow]
  have hfix (x : G) : σ x ≠ x := by
    intro h
    apply hne
    apply isConj_iff.mpr
    refine ⟨x⁻¹, ?_⟩
    change u⁻¹ * x * t = x at h
    calc
      x⁻¹ * u * (x⁻¹)⁻¹ = x⁻¹ * u * (u⁻¹ * x * t) := by rw [h, inv_inv]
      _ = t := by group
  let F := {x // σ x = x}
  let : IsEmpty F := ⟨fun x => hfix x.val x.property⟩
  have hsurj : Function.Surjective (localizationToResidue d) := by
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨algebraMap _ R a, localizationToResidue_algebraMap d a⟩
  have hf (r : R) (hr : localizationToResidue d r ≠ 0) : IsUnit r := by
    by_contra hn
    exact hr ((BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit d r).mpr hn)
  have hστ : Commute σ τ := by
    change σ * τ = τ * σ
    ext x
    simp only [σ, τ, Equiv.Perm.mul_apply, leftRightPerm_apply, inv_one, one_mul,
      mul_assoc]
    rw [htv.eq]
  have hτ : (τ.permMatrix R) ^ orderOf v = 1 := by
    rw [← Matrix.permMatrix_pow,
      leftRightPerm_pow_eq_one 1 v (one_pow _) (pow_orderOf_eq_one v)]
    simp
  obtain ⟨ζ, hζ⟩ := exists_localization_primitiveRoot d (orderOf v) (orderOf_dvd_natCard v)
  let : NeZero (orderOf v) := ⟨(orderOf_pos v).ne'⟩
  let : NeZero ((orderOf v : ℕ) : principalResidueField d) := ⟨by
    intro hz
    exact Nat.prime_two.coprime_iff_not_dvd.mp (Nat.coprime_two_left.mpr hv)
      ((CharP.cast_eq_zero_iff (principalResidueField d) 2 (orderOf v)).mp hz)⟩
  have httrace := Matrix.trace_permMatrix_mul_mul_eq_trace_fixed_lift
    (localizationToResidue d) hsurj hf σ hσ (rightMatrix e) (τ.permMatrix R)
    (rightMatrix_isIdempotent e (localizedPrincipalBlockElement_isIdempotent d))
    (rightMatrix_commute_leftRight e (localizedPrincipalBlockElement_mem_center d) u t)
    (Matrix.permMatrix_commute hστ)
    (rightMatrix_commute_leftRight e (localizedPrincipalBlockElement_mem_center d) 1 v)
    (0 : Matrix F F R) (1 : Matrix F F R) (by simp [IsIdempotentElem])
    (by exact Commute.one_left _)
    (by ext x; exact isEmptyElim x) (by ext x; exact isEmptyElim x)
    (orderOf_pos v) hτ (by simp)
    (isUnit_natCast_localization d _ (Nat.coprime_two_left.mpr hv)) hζ
    (BrauerCoefficientExtension.primitive_map (localizationToResidue d) hζ)
  have hfactor : σ.permMatrix R * τ.permMatrix R = (leftRightPerm u (t*v)).permMatrix R := by
    rw [← Matrix.permMatrix_mul]
    congr 1
    ext x
    simp [σ, τ, Equiv.Perm.mul_apply, mul_assoc]
  have htrace : LinearMap.trace R (MonoidAlgebra R G) (projectedLeftRight e u (t*v)) = 0 := by
    rw [hfactor, MixedBrauerTrace.trace_permMatrix_mul_rightMatrix] at httrace
    simpa using httrace
  have hc := congrArg (IsotypicLattice.localizationToComplex d) htrace
  rw [trace_projectedLeftRight, map_sum, map_zero] at hc
  rw [← principalBlock_leftRight_trace,
    ← mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement d
      (IsotypicLattice.localizationToComplex d) (IsotypicLattice.localizationToComplex_algebraMap d),
    trace_projectedLeftRight]
  exact hc

/-- The actual principal-block column kernel based at a two-element is supported on
its two-section. No subsection or decomposition-matrix hypotheses are required. -/
theorem principalBlock_column_eq_zero_of_not_mem_twoSection
    (d : PrincipalCongruenceBlockData G) (u : G)
    (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1) (g : G)
    (hsection : ¬ ∃ v : G, Odd (orderOf v) ∧ Commute u v ∧ IsConj (u * v) g) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk u) *
      star (d.chi i (ConjClasses.mk g)) = 0 := by
  obtain ⟨t, v, ht, hv, htv, rfl⟩ := exists_commuting_prime_parts 2 Nat.prime_two g
  have hvodd : Odd (orderOf v) :=
    Nat.coprime_two_left.mp (Nat.prime_two.coprime_iff_not_dvd.mpr hv)
  apply principalBlock_column_eq_zero_of_not_isConj_twoPart d u t v hu ht hvodd htv
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.mp h.symm
  let e := MulAut.conj c
  have he : e t = u := hc
  apply hsection
  refine ⟨e v, ?_, ?_, ?_⟩
  · simpa only [e.orderOf_eq] using hvodd
  · simpa only [he] using htv.map e
  · apply isConj_iff.mpr
    refine ⟨c⁻¹, ?_⟩
    rw [← he, ← map_mul]
    simp [e, MulAut.conj_apply, mul_assoc]

end ModularBlock.SectionOrthogonality
