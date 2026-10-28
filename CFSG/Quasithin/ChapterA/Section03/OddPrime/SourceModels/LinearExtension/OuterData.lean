module

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.FieldArithmetic
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualInner

/-!
# The component and outer parameters of the linear circle extension

The scalar kernel of GL₃ conjugation and a determinant correction identify
inner linear actors exactly with cube determinants. Coefficient rigidity
separates the field and diagonal outer images. Frobenius to degree 2n fixes
the diagonal image, so their independent mixed generator has order three.
Restricting the actual Aut-to-Out quotient then gives index three and the
cardinality comparison for the published `linearCircle` and its marked
component. The component equivalence retains the original inner map.

The first Frobenius inverts the diagonal outer parameter; this is the
identity used in the source's choice-independence argument. Existence of a
noncube follows from Cauchy's theorem in the finite field's unit group.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Notation A.3.16, printed p.51. The field exponent is the corrected one in
`SourceModels.FieldArithmetic`, including n = 1.
-/

@[expose] public section

open scoped MatrixGroups
open Matrix Subgroup Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open Matrix.PSL3.CartanActions
open Theory.GroupTheory.AutomorphismExtensionBorel
noncomputable section
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
variable {F : Type*} [Field F]

/-- The chosen diagonal matrix representative, multiplicative in its coefficient. -/
def circleDiagonalGL : Fˣ →* GL (Fin 3) F where
  toFun a := OddPrimeCoverage.diagonalGL ![a, 1, 1]
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> simp [OddPrimeCoverage.diagonalGL, Matrix.diagonal_apply, Matrix.one_apply]
  map_mul' a b := by
    apply Units.ext
    simp only [OddPrimeCoverage.diagonalGL, Units.val_mul, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp

theorem circleDiagonalGL_det (a : Fˣ) : GeneralLinearGroup.det (circleDiagonalGL a) = a := by
  apply Units.ext
  change Matrix.det (Matrix.diagonal _) = _
  simp [Matrix.det_diagonal, Fin.prod_univ_three]

/-- The corresponding element of the actual outer automorphism group. -/
def circleDiagonalOuter : Fˣ →* MulAut.Outer PSL(3,F) :=
  (linearOuterAction F).comp circleDiagonalGL

/-- A linear actor is inner exactly when its determinant is a cube. -/
theorem linearConj_inner_iff_det_cube (g : GL (Fin 3) F) :
    linearConj F g ∈ MulAut.innerSubgroup PSL(3,F) ↔
      ∃ r : Fˣ, r ^ 3 = GeneralLinearGroup.det g := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨s, rfl⟩ := Matrix.PSL3.projection_surjective F x
    have he : linearConj F (g * (SpecialLinearGroup.toGL s)⁻¹) = 1 := by
      change MulAut.conj (QuotientGroup.mk s) = linearConj F g at hx
      rw [map_mul, map_inv, linearConj_toGL, hx, mul_inv_cancel]
    have hz : g * (SpecialLinearGroup.toGL s)⁻¹ ∈ center (GL (Fin 3) F) := by
      rw [← linearConj_ker]
      exact he
    rw [GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨r, hr⟩ := hz
    refine ⟨r, ?_⟩
    have hd := congrArg GeneralLinearGroup.det hr
    simpa only [GeneralLinearGroup.det_scalar, Fintype.card_fin,
      map_mul, map_inv, SpecialLinearGroup.coeToGL_det, inv_one, mul_one] using hd
  · rintro ⟨r, hr⟩
    let m := GeneralLinearGroup.scalar (Fin 3) r⁻¹ * g
    have hm : GeneralLinearGroup.det m = 1 := by
      simp only [m, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin,
        inv_pow, hr, inv_mul_cancel]
    let s := (slEquivDetKernel F).symm ⟨m, hm⟩
    have hs : linearConj F (GeneralLinearGroup.scalar (Fin 3) r⁻¹) = 1 := by
      change GeneralLinearGroup.scalar (Fin 3) r⁻¹ ∈ (linearConj F).ker
      rw [linearConj_ker]
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨r⁻¹, rfl⟩
    refine ⟨Matrix.PSL3.projection F s, ?_⟩
    change MulAut.conj (QuotientGroup.mk s) = linearConj F g
    rw [← linearConj_toGL, slEquivDetKernel_symm_toGL]
    change linearConj F (GeneralLinearGroup.scalar (Fin 3) r⁻¹ * g) = _
    rw [map_mul, hs, one_mul]

/-- Every diagonal outer parameter has exponent dividing three. -/
theorem circleDiagonalOuter_cube (a : Fˣ) : circleDiagonalOuter a ^ 3 = 1 := by
  change qOuter F (linearConj F (circleDiagonalGL a)) ^ 3 = 1
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (ResidualInner.linearConj_cube_inner _)

/-- The kernel of the coefficient parameter is precisely the cubes. -/
theorem circleDiagonalOuter_eq_one_iff (a : Fˣ) :
    circleDiagonalOuter a = 1 ↔ ∃ r : Fˣ, r ^ 3 = a := by
  change qOuter F (linearConj F (circleDiagonalGL a)) = 1 ↔ _
  exact (QuotientGroup.eq_one_iff _).trans
    ((linearConj_inner_iff_det_cube _).trans (by rw [circleDiagonalGL_det]))

/-- A noncube coefficient represents an outer element of order three. -/
theorem circleDiagonalOuter_order (a : Fˣ) (ha : Noncube a) :
    orderOf (circleDiagonalOuter a) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime (circleDiagonalOuter_cube a)
  intro he
  obtain ⟨r, hr⟩ := (circleDiagonalOuter_eq_one_iff a).mp he
  exact ha r hr

/-- The determinant gives the exact diagonal outer parameter of every GL₃
representative. In particular changing a representative by an SL₃ matrix
does not change the mixed preimage. -/
theorem linearOuterAction_eq_circleDiagonal_det (g : GL (Fin 3) F) :
    linearOuterAction F g = circleDiagonalOuter (GeneralLinearGroup.det g) := by
  change linearOuterAction F g = linearOuterAction F (circleDiagonalGL (GeneralLinearGroup.det g))
  apply (linearOuterAction F).eq_iff.mpr
  apply det_ker_le_linearOuterAction_ker F
  change GeneralLinearGroup.det ((circleDiagonalGL (GeneralLinearGroup.det g))⁻¹ * g) = 1
  rw [map_mul, map_inv, circleDiagonalGL_det, inv_mul_cancel]

variable [CharP F 2]

/-- A field actor can be linear only when its coefficient automorphism is trivial. -/
theorem fieldAction_mem_innerDiagonal_iff (σ : F ≃+* F) :
    fieldAction F σ ∈ innerDiagonal F ↔ σ = 1 := by
  constructor
  · rintro ⟨g, hg⟩
    have hp : (linearConj F g⁻¹ * fieldAction F σ) ^ 1 = 1 := by
      rw [pow_one, ← hg, map_inv, inv_mul_cancel]
    simpa only [pow_one] using ResidualLinear.coefficient_pow_eq_one g⁻¹ σ hp
  · rintro rfl
    rw [map_one]
    exact (innerDiagonal F).one_mem

/-- Coefficient automorphisms remain faithful in the actual outer quotient. -/
theorem fieldOuter_injective : Function.Injective ((qOuter F).comp (fieldAction F)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro σ hσ
  have hi : fieldAction F σ ∈ MulAut.innerSubgroup PSL(3,F) :=
    (QuotientGroup.eq_one_iff _).mp hσ
  exact (fieldAction_mem_innerDiagonal_iff σ).mp (inner_le_innerDiagonal F hi)

variable [Finite F]

/-- Identify the marked component through its original inner-automorphism map. -/
def linearCircleComponentEquiv (n : ℕ) (a : Fˣ) :
    linearCircleComponent F n a ≃* PSL(3,F) :=
  (Subgroup.subgroupOfEquivOfLe (inner_le_linearCircle F n a)).trans
    (MonoidHom.ofInjective (inner_injective F)).symm

/-- The component identification preserves the literal embedding in Aut(PSL₃). -/
theorem linearCircleComponentEquiv_symm_coe (n : ℕ) (a : Fˣ) (x : PSL(3,F)) :
    ((linearCircleComponentEquiv n a).symm x).val.val = MulAut.conj x := rfl

/-- The source field actor retains order three after quotienting by inner actors. -/
theorem circleField_outer_order {n : ℕ} (hn : 0 < n) (hc : Nat.card F = 2 ^ (6 * n)) :
    orderOf (qOuter F (fieldAction F (circleField F n))) = 3 := by
  rw [← MonoidHom.comp_apply, orderOf_injective _ fieldOuter_injective]
  exact circleField_order hn hc

omit [Finite F] in
/-- Field and diagonal images have trivial intersection in the outer quotient. -/
theorem fieldOuter_mem_diagonal_iff (σ : F ≃+* F) :
    qOuter F (fieldAction F σ) ∈ innerDiagonalOuter F ↔ σ = 1 := by
  constructor
  · rintro ⟨g, hg⟩
    have hh : (linearConj F g)⁻¹ * fieldAction F σ ∈
        MulAut.innerSubgroup PSL(3,F) := by
      exact (QuotientGroup.eq_one_iff _).mp ((qOuter F).eq_iff.mp hg.symm)
    have hf : fieldAction F σ ∈ innerDiagonal F := by
      have hm := (innerDiagonal F).mul_mem (show linearConj F g ∈ innerDiagonal F from ⟨g, rfl⟩)
        (inner_le_innerDiagonal F hh)
      simpa only [mul_inv_cancel_left] using hm
    exact (fieldAction_mem_innerDiagonal_iff σ).mp hf
  · rintro rfl
    simp only [map_one]
    exact (innerDiagonalOuter F).one_mem

/-- The two source cyclic outer subgroups are independent. -/
theorem circle_outer_independent (n : ℕ) (a : Fˣ) :
    Disjoint (zpowers (qOuter F (fieldAction F (circleField F n))))
      (zpowers (circleDiagonalOuter a)) := by
  apply Subgroup.disjoint_def.mpr
  rintro x ⟨z, rfl⟩ hx
  have hd : (qOuter F (fieldAction F (circleField F n))) ^ z ∈ innerDiagonalOuter F :=
    (Subgroup.zpowers_le.mpr (show circleDiagonalOuter a ∈ innerDiagonalOuter F from
      ⟨circleDiagonalGL a, rfl⟩)) hx
  change (qOuter F (fieldAction F (circleField F n))) ^ z = 1
  rw [← map_zpow, ← map_zpow] at hd ⊢
  rw [(fieldOuter_mem_diagonal_iff _).mp hd, map_one, map_one]

omit [Finite F] [CharP F 2] in
private theorem field_circleDiagonal (σ : F ≃+* F) (a : Fˣ) :
    qOuter F (fieldAction F σ) * circleDiagonalOuter a =
      circleDiagonalOuter (Units.map σ.toMonoidHom a) * qOuter F (fieldAction F σ) := by
  have hm : GeneralLinearGroup.map σ.toRingHom (circleDiagonalGL a) =
      circleDiagonalGL (Units.map σ.toMonoidHom a) := by
    apply Units.ext
    change (Matrix.diagonal _).map σ = Matrix.diagonal _
    rw [Matrix.diagonal_map (map_zero σ)]
    congr 1
    ext i
    fin_cases i <;> simp
  have h := congrArg (qOuter F)
    (Matrix.PSL3.OuterSolvable.field_linearConj σ (circleDiagonalGL a))
  simpa only [hm, map_mul, circleDiagonalOuter, linearOuterAction, MonoidHom.comp_apply] using h

/-- In characteristic two, the first Frobenius inverts the diagonal outer
parameter. This is the conjugating actor in the source choice-independence
argument. -/
theorem frobenius_circleDiagonal_conj (a : Fˣ) :
    qOuter F (fieldAction F (frobeniusEquiv F 2)) * circleDiagonalOuter a *
      (qOuter F (fieldAction F (frobeniusEquiv F 2)))⁻¹ = (circleDiagonalOuter a)⁻¹ := by
  have hu : Units.map (frobeniusEquiv F 2).toMonoidHom a = a ^ 2 := by
    apply Units.ext
    rfl
  rw [field_circleDiagonal, hu, map_pow, mul_inv_cancel_right]
  apply mul_eq_one_iff_eq_inv.mp
  simpa only [← pow_succ] using circleDiagonalOuter_cube a

/-- The source coefficient actor on units is the expected Frobenius power. -/
theorem circleField_units (n : ℕ) (a : Fˣ) :
    Units.map (circleField F n).toMonoidHom a = a ^ (2 ^ (2 * n)) := by
  apply Units.ext
  change (circleField F n) (a : F) = (a : F) ^ (2 ^ (2 * n))
  rw [circleField, ← iterateFrobeniusEquiv_eq_pow]
  rfl

/-- The degree-2n Frobenius centralizes the diagonal outer parameter. -/
theorem circle_outer_commute (n : ℕ) (a : Fˣ) :
    Commute (qOuter F (fieldAction F (circleField F n))) (circleDiagonalOuter a) := by
  have hm : 2 ^ (2 * n) % 3 = 1 := by
    rw [pow_mul, Nat.pow_mod]
    norm_num
  change _ * _ = _ * _
  rw [field_circleDiagonal, circleField_units, map_pow,
    pow_eq_pow_mod _ (circleDiagonalOuter_cube a), hm, pow_one]

/-- The data used by the extension-Borel theorem are derived from the field
cardinality and the noncube coefficient, with no outer-order assumptions. -/
def linearCircleMixedData {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a) : MixedData F (6 * n) where
  six_dvd := dvd_mul_right 6 n
  coefficient := circleField F n
  diagonal := ![a, 1, 1]
  field_order := circleField_actor_order hn hc
  field_outer_order := circleField_outer_order hn hc
  diagonal_outer_order := circleDiagonalOuter_order a ha
  outer_commute := circle_outer_commute n a
  outer_independent := circle_outer_independent n a

/-- The source mixed outer generator has order exactly three. -/
theorem linearCircle_outer_order {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a) :
    orderOf (qOuter F (fieldAction F (circleField F n)) * circleDiagonalOuter a) = 3 :=
  mixed_outer_order F (linearCircleMixedData hn hc a ha)

/-- The marked component has index three in the published literal carrier. -/
theorem linearCircleComponent_index {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a) :
    (linearCircleComponent F n a).index = 3 := by
  change (MulAut.innerSubgroup PSL(3,F)).relIndex (linearCircle F n a) = 3
  rw [← QuotientGroup.ker_mk' (MulAut.innerSubgroup PSL(3,F)), Subgroup.relIndex_ker]
  change Nat.card ((zpowers _).comap (qOuter F) |>.map (qOuter F)) = 3
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    Nat.card_zpowers]
  exact linearCircle_outer_order hn hc a ha

/-- The order comparison needed by the source-model consumers. -/
theorem linearCircle_card {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a) :
    Nat.card (linearCircle F n a) = 3 * Nat.card PSL(3,F) := by
  rw [← (linearCircleComponent F n a).card_mul_index,
    linearCircleComponent_index hn hc a ha,
    Nat.card_congr (linearCircleComponentEquiv n a).toEquiv, Nat.mul_comm]

omit [CharP F 2] in
/-- Noncube coefficients exist at each source field cardinality. -/
theorem exists_noncube {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n)) :
    ∃ a : Fˣ, Noncube a := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hm : 2 ^ (6 * n) % 3 = 1 := by
    rw [pow_mul, Nat.pow_mod]
    norm_num
  have hd : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hc]
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 hd
  by_contra! h
  have hs : Function.Surjective (fun a : Fˣ => a ^ 3) := by
    intro a
    simpa only [Noncube, not_forall, not_not] using h a
  have hi := (Finite.injective_iff_surjective).mpr hs
  have he : u = 1 := hi (by
    change u ^ 3 = (1 : Fˣ) ^ 3
    rw [← hu, pow_orderOf_eq_one, one_pow])
  rw [he, orderOf_one] at hu
  norm_num at hu

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
