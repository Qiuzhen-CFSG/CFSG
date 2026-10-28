module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Geometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorKernel
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus

/-!
# The quadratic descent model for the minus-six/unitary-four comparison

Let E be GF(2^(2n)) and k its actual 2^n-Frobenius fixed field. The
six-dimensional k-space k⁴ ⊕ E has quadratic form two hyperbolic planes
plus the extension norm. It embeds in the six bivector coordinates as
(a,c,z,z^q,d,b); the exterior Pfaffian restricts to exactly this form.
The four-dimensional Hermitian form is the existing antidiagonal form.

These are shared concrete coordinates for the twisted A₃/D₃ comparison.
Group invariance and exhaustion of the orthogonal commutator remain separate
proof obligations. Sources: GLS3 §2.7; Aschbacher–Smith A.2.18, printed p.40,
and Theorem D, printed pp.1078–1079. The exterior maps and their scalar-kernel
theorem are reused from the attributed ATLAS port, without modifying it.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open Atlas.Order20160A8.Bivectors
open Representation.OrthogonalFourMinus

abbrev Field (n : ℕ) := FiniteModel.Field n
abbrev FixedField (n : ℕ) := FiniteModel.fixedField n
abbrev conjugation (n : ℕ) := FiniteModel.conjugation n

variable (n : ℕ) [NeZero n]

/-- The coefficient field has square of the unitary parameter as its order. -/
theorem card_field : Nat.card (Field n) = (2 ^ n) ^ 2 := by
  rw [GaloisField.card 2 (2 * n) (Nat.mul_ne_zero (by decide) (NeZero.ne n)),
    ← pow_mul, Nat.mul_comm n 2]

/-- The fixed field has the unitary parameter as its order. -/
theorem card_fixedField : Nat.card (FixedField n) = 2 ^ n := FiniteModel.card_fixedField n

/-- The literal antidiagonal Hermitian form over the quadratic extension. -/
def unitaryForm : HermitianForm 4 (Field n) :=
  UnitaryFourFlag.form (Field n) (conjugation n) (FiniteModel.conjugation_involutive n)

@[simp] theorem unitaryForm_conj (x : Field n) :
    (unitaryForm n).conj x = x ^ (2 ^ n) := iterateFrobeniusEquiv_def ..

abbrev SU := (unitaryForm n).specialSubgroup

/-- SU₄ with its genuine entries and determinant-one condition. -/
def toSL : SU n →* SpecialLinearGroup (Fin 4) (Field n) where
  toFun g := ⟨g.val.val, congrArg Units.val g.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toSL_injective : Function.Injective (toSL n) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val he

/-- The exterior action before descent, using the actual second compound matrix. -/
def exterior : SU n →* (Six (Field n) ≃ₗ[Field n] Six (Field n)) where
  toFun g := Atlas.Order20160A8.Exterior.exteriorAction (toSL n g)
  map_one' := by
    apply LinearEquiv.ext
    intro w
    exact congrArg (fun f : Six (Field n) →ₗ[Field n] Six (Field n) => f w)
      exteriorMap_one
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    exact congrArg (fun f : Six (Field n) →ₗ[Field n] Six (Field n) => f w)
      (exteriorMap_mul g.val.val h.val.val)

@[simp] theorem exterior_apply (g : SU n) (w : Six (Field n)) :
    exterior n g w = exteriorMap g.val.val w := rfl

theorem exterior_pfaffian (g : SU n) (w : Six (Field n)) :
    pfaffian (exterior n g w) = pfaffian w := by
  have hd : g.val.val.det = 1 := (toSL n g).det_coe
  rw [exterior_apply, pfaffian_exteriorMap, hd, one_mul]

/-- In characteristic two the exterior square has no scalar kernel. -/
theorem exterior_injective : Function.Injective (exterior n) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨c, hc, hcg⟩ := scalar_of_exteriorMap_eq_id g.val.val
    (fun w => LinearEquiv.congr_fun hg w)
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hc with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  apply Subtype.ext
  apply Units.ext
  change g.val.val = 1
  simpa only [hc1, one_smul] using hcg

/-- Two hyperbolic planes and one extension-field coordinate. -/
abbrev Space := (Fin 2 → FixedField n × FixedField n) × Field n

/-- The extension norm as a quadratic form over the actual fixed field. -/
def normForm : QuadraticForm (FixedField n) (Field n) :=
  -(FiniteModel.form n).comp ((FiniteModel.coordinates n).symm.toLinearMap.comp
    (LinearMap.inr (FixedField n) (FixedField n × FixedField n) (Field n)))

@[simp] theorem normForm_apply (z : Field n) : normForm n z = FiniteModel.norm n z := by
  change -(FiniteModel.form n ((FiniteModel.coordinates n).symm ((0, 0), z))) = _
  rw [FiniteModel.form_coordinates]
  simp

/-- The norm form is anisotropic, including in characteristic two. -/
theorem normForm_anisotropic : (normForm n).Anisotropic := by
  intro z hz
  exact (FiniteModel.norm_eq_zero_iff n z).mp ((normForm_apply n z).symm.trans hz)

/-- The quadratic form that the descended exterior-square action must preserve. -/
def form : QuadraticForm (FixedField n) (Space n) :=
  (QuadraticMap.pi fun _ : Fin 2 => Minus.hyperbolic (FixedField n)).prod (normForm n)

@[simp] theorem form_apply (v : Space n) :
    form n v = (v.1 0).1 * (v.1 0).2 + (v.1 1).1 * (v.1 1).2 + FiniteModel.norm n v.2 := by
  simp [form, QuadraticMap.pi_apply, Fin.sum_univ_succ]

theorem space_finrank : Module.finrank (FixedField n) (Space n) = 6 := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_prod, FiniteModel.finrank_field]
  simp

/-- The six bivector coordinates 01,02,03,12,13,23 of a descended vector. -/
def toBivector : Space n →ₗ[FixedField n] Six (Field n) where
  toFun v := ![(v.1 0).1, (v.1 1).1, v.2, conjugation n v.2, (v.1 1).2, (v.1 0).2]
  map_add' v w := by
    ext i
    fin_cases i <;> simp
  map_smul' c v := by
    have hc : conjugation n (c : Field n) = (c : Field n) := c.property
    ext i
    fin_cases i <;> simp [Subfield.smul_def, map_mul, hc]

omit [NeZero n] in
theorem toBivector_injective : Function.Injective (toBivector n) := by
  intro v w h
  apply Prod.ext
  · funext i
    apply Prod.ext
    · fin_cases i
      · exact Subtype.ext (congrFun h 0)
      · exact Subtype.ext (congrFun h 1)
    · fin_cases i
      · exact Subtype.ext (congrFun h 5)
      · exact Subtype.ext (congrFun h 4)
  · exact congrFun h 2

/-- The ambient Pfaffian has the required minus quadratic values after descent. -/
theorem pfaffian_toBivector (v : Space n) :
    pfaffian (toBivector n v) = (form n v : Field n) := by
  simp [toBivector, form_apply, pfaffian_apply, FiniteModel.norm, CharTwo.sub_eq_add]

/-- The actual subspace on which the unitary exterior square must descend. -/
def descentSpace : Submodule (FixedField n) (Six (Field n)) := (toBivector n).range

/-- Concrete coordinates on the descent subspace; this is not an assumed action. -/
def descentEquiv : Space n ≃ₗ[FixedField n] descentSpace n :=
  LinearEquiv.ofInjective (toBivector n) (toBivector_injective n)

omit [NeZero n] in
@[simp] theorem descentEquiv_apply (v : Space n) :
    (descentEquiv n v).val = toBivector n v := rfl

omit [NeZero n] in
/-- Its four scalar coordinates are fixed, and its middle pair is conjugate. -/
theorem mem_descentSpace (w : Six (Field n)) : w ∈ descentSpace n ↔
    conjugation n (w 0) = w 0 ∧ conjugation n (w 1) = w 1 ∧
    conjugation n (w 4) = w 4 ∧ conjugation n (w 5) = w 5 ∧
    conjugation n (w 2) = w 3 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(v.1 0).1.property, (v.1 1).1.property,
      (v.1 1).2.property, (v.1 0).2.property, rfl⟩
  · rintro ⟨h0, h1, h4, h5, h23⟩
    refine ⟨(![(⟨w 0, h0⟩, ⟨w 5, h5⟩), (⟨w 1, h1⟩, ⟨w 4, h4⟩)], w 2), ?_⟩
    ext i
    fin_cases i <;> simp [toBivector, h23]

/-- The descended vectors span all bivectors after extending scalars to E.
Consequently equivariance on these coordinates determines the full exterior action. -/
theorem bivector_ext {W : Type*} [AddCommGroup W] [Module (Field n) W]
    {L M : Six (Field n) →ₗ[Field n] W}
    (h : ∀ v : Space n, L (toBivector n v) = M (toBivector n v)) : L = M := by
  obtain ⟨t, ht⟩ := FiniteModel.exists_conjugation_ne n
  have hden : conjugation n t - t ≠ 0 := sub_ne_zero.mpr ht
  have he3 : (Pi.single 3 (1 : Field n) : Six (Field n)) =
      (conjugation n t - t)⁻¹ • toBivector n (0, t) -
        (t / (conjugation n t - t)) • toBivector n (0, 1) := by
    ext i
    fin_cases i <;> simp [toBivector, div_eq_mul_inv]
    · ring
    · field_simp
  have h3 : L (Pi.single 3 1) = M (Pi.single 3 1) := by
    rw [he3, map_sub, map_sub, map_smul, map_smul, map_smul, map_smul, h, h]
  have he2 : (Pi.single 2 (1 : Field n) : Six (Field n)) =
      toBivector n (0, 1) - Pi.single 3 1 := by
    ext i
    fin_cases i <;> simp [toBivector]
  have h2 : L (Pi.single 2 1) = M (Pi.single 2 1) := by
    rw [he2, map_sub, map_sub, h, h3]
  apply (Pi.basisFun (Field n) (Fin 6)).ext
  intro i
  simp only [Pi.basisFun_apply]
  change L (Pi.single i 1) = M (Pi.single i 1)
  fin_cases i
  · convert h (![(1,0),(0,0)], 0) using 1 <;>
      congr 1 <;> ext j <;> fin_cases j <;> simp [toBivector]
  · convert h (![(0,0),(1,0)], 0) using 1 <;>
      congr 1 <;> ext j <;> fin_cases j <;> simp [toBivector]
  · exact h2
  · exact h3
  · convert h (![(0,0),(0,1)], 0) using 1 <;>
      congr 1 <;> ext j <;> fin_cases j <;> simp [toBivector]
  · convert h (![(0,1),(0,0)], 0) using 1 <;>
      congr 1 <;> ext j <;> fin_cases j <;> simp [toBivector]

end ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
