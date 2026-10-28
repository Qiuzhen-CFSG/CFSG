module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.MixedCoordinates
import Mathlib.Tactic.Ring

/-!
# Explicit mixed extensions of the binary natural and dual SL₃(4) modules

The two-parameter formula `mixedValue p q` is a normalized central block cocycle.
Its first matrix identity follows by expanding row products and the three-by-three
cofactor formula, using characteristic two and `x⁴ = x` in F₄. Applying Frobenius
and transpose to the identity at the inverse elements proves the second identity.
This retains the inverse in `dualSymmetricMatrix`.

A splitting would give a binary linear section change. Evaluating it on the root
`x₀₁(t)` and vectors on the third and first coordinate axes forces the two
parameters to be zero: varying the root parameter and the vector coordinate
separates squaring from multiplication by a field scalar. Conversely the zero
parameter gives the actual direct-sum representation. Ordinary F₄ scalars in
these formulas are distinct from the canonical central-field structures.

Source context: James (1973), Lemma 8.3, and Aschbacher–Smith, H.12.1,
printed pp.393–394. The point restriction on p.394 is an extension of the
natural module by its dual. This module constructs the mixed family and proves
its splitting criterion; exhaustive coverage is a separate result.
-/

@[expose] public noncomputable section

namespace Representation.SL3FourLocalCatalogue.ExtensionCoordinates
open Matrix

/-- The symmetric-square cross term satisfies the matrix cocycle identity. -/
lemma symmetricMatrix_mul (g h : SL) : symmetricMatrix (g*h) =
    g.val * symmetricMatrix h + symmetricMatrix g * ((h⁻¹).val.transpose.map (fun x => x^2)) := by
  funext i j
  simp only [symmetricMatrix, Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply,
    Matrix.transpose_apply, Matrix.SpecialLinearGroup.coe_mul, Fin.sum_univ_three]
  simp only [mul_pow, CharTwo.add_sq]
  change _ = _ + (_ * ((h⁻¹).val j 0)^2 + _ * ((h⁻¹).val j 1)^2 + _ * ((h⁻¹).val j 2)^2)
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
  fin_cases j <;>
    simp [CharTwo.sub_eq_add, CharTwo.neg_eq, CharTwo.add_sq, mul_pow] <;>
    ring_nf <;> simp only [SL2FourNatural.pow_four] <;> ring

/-- Binary duality gives the second matrix cocycle identity. -/
lemma dualSymmetricMatrix_mul (g h : SL) : dualSymmetricMatrix (g*h) =
    g.val * dualSymmetricMatrix h + dualSymmetricMatrix g *
      ((h⁻¹).val.transpose.map (fun x => x^2)) := by
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) F =>
    M.transpose.map SL2FourNatural.fieldFrobenius) (symmetricMatrix_mul h⁻¹ g⁻¹)
  simp only [Matrix.transpose_add, Matrix.transpose_mul, inv_inv] at he
  rw [← _root_.mul_inv_rev] at he
  change dualSymmetricMatrix (g*h) = _ at he
  rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul] at he
  have hf : ((g.val.transpose.map (fun x => x^2)).transpose.map
      SL2FourNatural.fieldFrobenius) = g.val := by
    funext i j
    exact SL2FourNatural.fieldFrobenius_involutive _
  rw [hf] at he
  exact he.trans (add_comm _ _)

/-- The complete multiplication law for every pair of parameters and group elements. -/
lemma mixedValue_mul (p q : F) (g h : SL) : mixedValue p q (g*h) =
    (constituent .natural g).comp (mixedValue p q h) +
      (mixedValue p q g).comp (constituent .dual h) := by
  apply LinearMap.ext
  intro v
  funext i
  change ((p • symmetricMatrix (g*h) + q • dualSymmetricMatrix (g*h)).mulVec
    (squareVector v)) i =
    (g.val.mulVec ((p • symmetricMatrix h + q • dualSymmetricMatrix h).mulVec
      (squareVector v))) i +
    ((p • symmetricMatrix g + q • dualSymmetricMatrix g).mulVec
      (squareVector ((h⁻¹).val.transpose.mulVec v))) i
  have hs : squareVector ((h⁻¹).val.transpose.mulVec v) =
      ((h⁻¹).val.transpose.map (fun x => x^2)).mulVec (squareVector v) := by
    funext j
    exact RingHom.map_mulVec SL2FourNatural.fieldFrobenius.toRingHom (h⁻¹).val.transpose v j
  rw [hs, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, symmetricMatrix_mul, dualSymmetricMatrix_mul]
  simp only [smul_add, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The explicit natural-by-dual mixed extension with two field parameters. -/
def mixedCocycle (p q : F) : BlockCocycle .natural .dual where
  value := mixedValue p q
  one := mixedValue_one p q
  mul := mixedValue_mul p q

/-- The packaged cocycle has the prescribed value on every group element. -/
lemma mixedCocycle_value (p q : F) (g : SL) :
    (mixedCocycle p q).value g = mixedValue p q g := rfl

/-- The mixed cocycle is normalized at the central scalar. -/
lemma mixedCocycle_value_z (p q : F) : (mixedCocycle p q).value z = 0 :=
  mixedValue_z p q

/-- Every member of the mixed family satisfies the central quadratic condition. -/
lemma mixedCocycle_isCentral (p q : F) : (mixedCocycle p q).IsCentral :=
  BlockCocycle.isCentral_of_value_z_eq_zero _ (mixedCocycle_value_z p q)

/-- The central polynomial holds on the whole mixed representation. -/
lemma mixedCocycle_centralQuadratic (p q : F) :
    CentralQuadratic (mixedCocycle p q).representation :=
  (mixedCocycle p q).centralQuadratic_iff.mpr (mixedCocycle_isCentral p q)

/-- The zero parameter has identically zero cross block. -/
lemma mixedValue_zero (g : SL) : mixedValue 0 0 g = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  simp [mixedValue_apply]

private lemma natural_transvection {i j : Fin 3} (hij : i ≠ j) (a : F) (v : W) :
    constituent .natural (SpecialLinearGroup.transvection hij a) v =
      v + Pi.single i (a * v j) := by
  change ((1 : Matrix (Fin 3) (Fin 3) F) + Matrix.single i j a).mulVec v = _
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

private lemma dual_transvection {i j : Fin 3} (hij : i ≠ j) (a : F) (v : W) :
    constituent .dual (SpecialLinearGroup.transvection hij a) v =
      v + Pi.single j (a * v i) := by
  change ((SpecialLinearGroup.transvection hij a)⁻¹).val.transpose.mulVec v = _
  rw [SpecialLinearGroup.transvection_inv, CharTwo.neg_eq,
    SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  congr 1
  funext k
  by_cases hk : k = j <;> simp [hk]

/-- A binary linear splitting of the mixed block forces both parameters to vanish. -/
lemma mixedValue_parameters_eq_zero_of_coboundary (p q : F) (f : W →ₗ[ZMod 2] W)
    (hf : ∀ g, mixedValue p q g + f.comp (constituent .dual g) =
      (constituent .natural g).comp f) : p = 0 ∧ q = 0 := by
  have hr (t : F) (v : W) :
      p • Pi.single (0 : Fin 3) (t^2 * (v 2)^2) +
        q • Pi.single (2 : Fin 3) (t * (v 0)^2) +
        f (Pi.single 1 (t * v 0)) = Pi.single 0 (t * f v 1) := by
    have he := LinearMap.congr_fun (hf (SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) t)) v
    change mixedValue p q _ v + f ((constituent .dual _) v) =
      (constituent .natural _) (f v) at he
    rw [mixedValue_transvection (k := 2) (by decide) (by decide) (by decide),
      natural_transvection, dual_transvection, map_add] at he
    linear_combination (norm := abel) he
  have hp (t : F) : p * t^2 = t * f (Pi.single 2 1) 1 := by
    simpa using congrFun (hr t (Pi.single 2 1)) 0
  have hq (t s : F) : q * (t * s^2) + f (Pi.single 1 (t*s)) 2 = 0 := by
    simpa using congrFun (hr t (Pi.single 0 s)) 2
  have hw : SL3FourNaturalDual.omega ^ 2 - SL3FourNaturalDual.omega ≠ 0 := by decide +kernel
  constructor
  · apply (mul_eq_zero.mp (show p * (SL3FourNaturalDual.omega^2 -
        SL3FourNaturalDual.omega) = 0 from ?_)).resolve_right hw
    linear_combination hp SL3FourNaturalDual.omega - SL3FourNaturalDual.omega * hp 1
  · apply (mul_eq_zero.mp (show q * (SL3FourNaturalDual.omega^2 -
        SL3FourNaturalDual.omega) = 0 from ?_)).resolve_right hw
    have he := hq 1 SL3FourNaturalDual.omega
    have he' := hq SL3FourNaturalDual.omega 1
    simp only [one_mul, one_pow, mul_one] at he he'
    linear_combination he - he'

/-- Exactly the zero parameter admits a binary linear change of section to a split block. -/
theorem mixedValue_coboundary_iff (p q : F) :
    (∃ f : W →ₗ[ZMod 2] W, ∀ g : SL,
      mixedValue p q g + f.comp (constituent .dual g) =
        (constituent .natural g).comp f) ↔ p = 0 ∧ q = 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact mixedValue_parameters_eq_zero_of_coboundary p q f hf
  · rintro ⟨rfl, rfl⟩
    exact ⟨0, fun g => by simp [mixedValue_zero]⟩

/-- The cocycle at zero is the split block cocycle. -/
lemma mixedCocycle_zero : mixedCocycle 0 0 = BlockCocycle.zero .natural .dual := by
  apply BlockCocycle.ext_transvections
  intro i j hij t
  exact mixedValue_zero _

/-- The representation at zero is the specified direct sum of the two constituents. -/
lemma mixedCocycle_zero_representation :
    (mixedCocycle 0 0).representation = splitRepresentation .natural .dual := by
  rw [mixedCocycle_zero, BlockCocycle.zero_representation]

/-- An actual intertwining linear equivalence identifies the zero parameter with the split model. -/
def mixedCocycle_zero_equiv :
    (mixedCocycle 0 0).representation.Equiv (splitRepresentation .natural .dual) := by
  rw [mixedCocycle_zero_representation]
  exact Representation.Equiv.refl _

end Representation.SL3FourLocalCatalogue.ExtensionCoordinates
