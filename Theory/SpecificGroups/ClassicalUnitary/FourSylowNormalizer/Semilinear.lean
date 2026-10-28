module
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer.Basic
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.CommutatorImage.NormPlane
public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Algebra.ZMod

/-!
# Solvable semilinear actions on the unitary norm plane

Scalar multiples of field automorphisms form the image of the semidirect
product of field units with the cyclic finite-field automorphism group,
so their additive action is solvable. A norm-semilinear additive bijection
belongs to this group: extend its fixed-field automorphism by Frobenius,
then divide out that automorphism and its value at one. The remaining
norm isometry is either the identity or the field involution.

The root-normalizer application uses the intrinsic norm identity on its
parameter action. Source: Aschbacher--Smith F.1.11--12 and the solvable
Sylow-automorphism argument of 4.4.10--11, printed pp.262--264 and 621.
-/

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer
variable (F : Type*) [Field F]

private def unitAction : (F ≃+* F) →* MulAut Fˣ where
  toFun φ := Units.mapEquiv φ.toMulEquiv
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

private abbrev Parameters := Fˣ ⋊[unitAction F] (F ≃+* F)

private def parameterMap (p : Parameters F) : F ≃+ F where
  toFun x := (p.left : F) * p.right x
  invFun x := p.right.symm ((↑p.left⁻¹ : F) * x)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp [mul_add]

private def parametersHom : Parameters F →* MulAut (Multiplicative F) where
  toFun p := AddEquiv.toMultiplicative (parameterMap F p)
  map_one' := by ext x; change (1:F)*x.toAdd=x.toAdd; simp
  map_mul' p q := by
    ext x
    change ((p.left * unitAction F p.right q.left : Fˣ) : F) *
      p.right (q.right x.toAdd) =
      (p.left : F)*p.right ((q.left : F)*q.right x.toAdd)
    simp only [Units.val_mul, map_mul, mul_assoc]
    rfl

/-- Additive automorphisms that are scalar multiples of field automorphisms. -/
def fieldSemilinear : Subgroup (MulAut (Multiplicative F)) := (parametersHom F).range

theorem mem_fieldSemilinear (s : MulAut (Multiplicative F)) :
    s ∈ fieldSemilinear F ↔ ∃ φ : F ≃+* F, ∀ x,
      (s (Multiplicative.ofAdd x)).toAdd =
      (s (Multiplicative.ofAdd 1)).toAdd * φ x := by
  constructor
  · rintro ⟨p,rfl⟩
    refine ⟨p.right,fun x => ?_⟩
    change (p.left : F)*p.right x = ((p.left : F)*p.right 1)*p.right x
    rw [map_one,mul_one]
  · rintro ⟨φ,hφ⟩
    have hc : (s (Multiplicative.ofAdd 1)).toAdd ≠ 0 := by
      intro h
      have he : s (Multiplicative.ofAdd 1) = 1 := congrArg Multiplicative.ofAdd h
      have hb := s.injective (he.trans s.map_one.symm)
      exact one_ne_zero (congrArg Multiplicative.toAdd hb)
    refine ⟨⟨Units.mk0 _ hc,φ⟩,?_⟩
    ext x
    exact (hφ x.toAdd).symm

/-- The scalar kernel is abelian and the finite-field quotient is cyclic. -/
theorem fieldSemilinear_isSolvable [Finite F] : Group.IsSolvable (fieldSemilinear F) := by
  let : Group.IsSolvable (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isSolvable
  let : Group.IsSolvable (Parameters F) :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl
      SemidirectProduct.rightHom SemidirectProduct.range_inl_eq_ker_rightHom.ge
  exact Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective (parametersHom F))

variable [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

private theorem extend_fixed_aut (τ : FixedField F σ ≃+* FixedField F σ) :
    ∃ φ : F ≃+* F, (∀ t : FixedField F σ, φ (t : F) = (τ t : F)) ∧
      ∀ x, φ (σ x) = σ (φ x) := by
  let K := FixedField F σ
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let τ' : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := τ) (by
    intro x
    exact DFunLike.congr_fun (RingHom.ext_zmod
      (τ.toRingHom.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K)) x)
  obtain ⟨i,hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    (ZMod 2) K).surjective τ'
  have hτ (x : K) : τ x = x ^ (2 ^ (i : ℕ)) := by
    have hx := DFunLike.congr_fun hi x
    change (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^ (i : ℕ)) x = τ x at hx
    simpa only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
      pow_iterate, ZMod.card] using hx.symm
  let φ : F ≃+* F :=
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ (i : ℕ)).toRingEquiv
  have hφ (x : F) : φ x = x ^ (2 ^ (i : ℕ)) := by
    simp only [φ, AlgEquiv.coe_ringEquiv, AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, ZMod.card]
  refine ⟨φ, ?_, ?_⟩
  · intro t
    rw [hφ,hτ]
    rfl
  · intro x
    rw [hφ,hφ,map_pow]

omit [Finite F] [CharP F 2] in
private theorem norm_mul_local (x y : F) :
    norm F σ hσ (x*y) = norm F σ hσ x * norm F σ hσ y := by
  apply Subtype.ext
  simp only [norm_val, Subfield.coe_mul, map_mul]
  ring

/-- A norm-semilinear additive bijection is scalar times a field automorphism. -/
theorem semilinear_norm_normal_form (L : F ≃+ F)
    (τ : FixedField F σ ≃+* FixedField F σ)
    (_hnt : ∃ u, σ u ≠ u)
    (_hlin : ∀ (t : FixedField F σ) (x : F), L ((t : F)*x) = (τ t : F)*L x)
    (hN : ∀ x, norm F σ hσ (L x) = norm F σ hσ (L 1)*τ (norm F σ hσ x)) :
    ∃ φ : F ≃+* F, ∀ x, L x = L 1 * φ x := by
  obtain ⟨φ,hφK,hφσ⟩ := extend_fixed_aut F σ τ
  have hc : L 1 ≠ 0 := fun h => one_ne_zero (L.injective (h.trans L.map_zero.symm))
  have hn : norm F σ hσ (L 1) ≠ 0 := by
    intro h
    have hz := congrArg Subtype.val h
    change σ (L 1) * L 1 = 0 at hz
    exact (mul_ne_zero (fun h => hc (σ.injective (h.trans σ.map_zero.symm))) hc) hz
  have hNφ (x : F) : norm F σ hσ (φ x) = τ (norm F σ hσ x) := by
    apply Subtype.ext
    rw [norm_val, ← hφK, norm_val, map_mul, hφσ]
  let A : F →+ F :=
    { toFun := fun z => (L 1)⁻¹ * L (φ.symm z)
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add] }
  have hA1 : A 1 = 1 := by simp [A,hc]
  have hAN (z : F) : norm F σ hσ (A z) = norm F σ hσ z := by
    change norm F σ hσ ((L 1)⁻¹ * L (φ.symm z)) = _
    rw [norm_mul_local,hN,← hNφ,φ.apply_symm_apply]
    have hinv : norm F σ hσ ((L 1)⁻¹) = (norm F σ hσ (L 1))⁻¹ := by
      apply Subtype.ext
      simp only [norm_val, Subfield.coe_inv, map_inv₀, mul_inv]
    rw [hinv,← mul_assoc,inv_mul_cancel₀ hn,one_mul]
  have hAN' (z : F) :
      ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel.norm σ hσ (A z) =
      ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel.norm σ hσ z := by
    apply Subtype.ext
    have h := congrArg Subtype.val (hAN z)
    simpa only [norm_val,ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel.norm,
      mul_comm] using h
  obtain ⟨u,hu,h | h⟩ :=
    ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel.norm_isometry_normal_form
      σ hσ A hAN'
  · have hu1 : u = 1 := by simpa only [hA1,mul_one] using (h 1).symm
    refine ⟨φ,fun x => ?_⟩
    have hx := congrArg (L 1 * ·) (h (φ x))
    simpa only [A, AddMonoidHom.coe_mk, ZeroHom.coe_mk, φ.symm_apply_apply, hu1,
      one_mul, ← mul_assoc, mul_inv_cancel₀ hc] using hx
  · have hu1 : u = 1 := by simpa only [hA1,map_one,mul_one] using (h 1).symm
    refine ⟨σ * φ,fun x => ?_⟩
    change L x = L 1 * σ (φ x)
    have hx := congrArg (L 1 * ·) (h (φ x))
    simpa only [A, AddMonoidHom.coe_mk, ZeroHom.coe_mk, φ.symm_apply_apply, hu1,
      one_mul, ← mul_assoc, mul_inv_cancel₀ hc] using hx

end Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer
