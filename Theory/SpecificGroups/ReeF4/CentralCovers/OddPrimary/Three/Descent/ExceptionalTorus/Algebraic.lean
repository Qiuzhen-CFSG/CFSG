module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus.Weyl
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic.FixedModel
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Lang conjugation and finite descent of the marked Ree torus

Embed both finite fields in the specified algebraic closure of GF(q²).
The full norm-one product maps faithfully to the concrete algebraic F₄
torus. The preceding Weyl equation and the norm-one identity prove its
fixedness under the conjugated exceptional twist. The proved zero-differential
Lang theorem supplies the named conjugator for m ≥ 1.

The checked rational-descent equivalence then places every element in the
actual finite root-generated Ree model. `modelMap_marking` retains the
literal coefficient embedding and conjugation equation for later extensions.
No unitary-group embedding or projective quotient is an input.

Sources: GLS3 Example 2.6.3 and Table 4.7.3A; Steinberg's rational descent
and Lang theorem, reused through `Cyclotomic.FixedModel` and `AlgebraicTwist`.
-/

@[expose] public section
open Theory.AlgebraicGroup
namespace ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus
open ReeF4.CentralCovers.OddPrimary.Cyclotomic
open ReeF4.BinaryDegree.ExceptionalTensor.Classification
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

def normUnitHom (m : ℕ) (f : QuadraticField m →+* F) :
    BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne (form m) →* Fˣ :=
  (Units.map f.toMonoidHom).comp
    (BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne (form m)).subtype

omit [IsAlgClosed F] [CharP F 2] in
theorem normUnitHom_injective (m : ℕ) (f : QuadraticField m →+* F) :
    Function.Injective (normUnitHom m f) := by
  intro a b h
  apply Subtype.ext
  apply Units.ext
  exact f.injective (congrArg Units.val h)

omit [IsAlgClosed F] [CharP F 2] in
theorem normUnitHom_pow (m : ℕ) (f : QuadraticField m →+* F)
    (a : BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne (form m)) :
    (normUnitHom m f a) ^ (2 * signedExponent m ^ 2 + 1) = 1 := by
  rw [signedExponent_square,
    show ((2^(2*m+1) : ℕ) : ℤ) + 1 = ↑(2^(2*m+1)+1 : ℕ) by omega, zpow_natCast]
  apply Units.ext
  change (f (a.val : QuadraticField m)) ^ (2 ^ (2*m+1) + 1) = 1
  rw [← map_pow]
  have ha : (a.val : QuadraticField m) ^ (2 ^ (2*m+1)) = (a.val : QuadraticField m)⁻¹ := a.property
  rw [pow_succ, ha, inv_mul_cancel₀ a.val.ne_zero, map_one]

/-- The full product of norm-one groups, transported by the displayed field embedding. -/
def parameterHom (m : ℕ) (f : QuadraticField m →+* F) :
    Parameters m →* (Fˣ × Fˣ) :=
  (normUnitHom m f).prodMap (normUnitHom m f)

omit [IsAlgClosed F] [CharP F 2] in
theorem parameterHom_injective (m : ℕ) (f : QuadraticField m →+* F) :
    Function.Injective (parameterHom m f) := by
  intro a b h
  exact Prod.ext (normUnitHom_injective m f (congrArg Prod.fst h))
    (normUnitHom_injective m f (congrArg Prod.snd h))

/-- The diagonal convention is the inverse of the positive coroot convention. -/
def algebraicMap (m : ℕ) (f : QuadraticField m →+* F) :
    Parameters m →* AlgebraicPoints F :=
  diagonal.comp ((invMonoidHom : (Fin 4 → Fˣ) →* (Fin 4 → Fˣ)).comp
    ((coordinateHom m).comp (parameterHom m f)))

omit [CharP F 2] in
theorem algebraicMap_injective (m : ℕ) (f : QuadraticField m →+* F) :
    Function.Injective (algebraicMap m f) :=
  diagonal_injective.comp (inv_injective.comp
    ((coordinateHom_injective m).comp (parameterHom_injective m f)))

theorem algebraicMap_twisted_fixed (m : ℕ) (f : QuadraticField m →+* F) (a : Parameters m) :
    normalizer m * (algebraicReeTwist m).onPoints (algebraicMap m f a) *
        (normalizer m)⁻¹ = algebraicMap m f a := by
  change normalizer m * (algebraicReeTwist m).onPoints
      (diagonal ((coordinates m (normUnitHom m f a.1) (normUnitHom m f a.2))⁻¹)) *
        (normalizer m)⁻¹ = _
  rw [normalizer_twist, map_inv,
    coordinates_fixed m _ _ (normUnitHom_pow m f a.1) (normUnitHom_pow m f a.2)]
  rfl

/-- A chosen Lang solution for the literal Weyl representative. -/
def conjugator (m : ℕ) (hm : 1 ≤ m) : AlgebraicPoints F :=
  Classical.choose (algebraicReeTwist_lang (F := F) m hm (normalizer m))

theorem conjugator_equation (m : ℕ) (hm : 1 ≤ m) :
    conjugator (F := F) m hm *
      ((algebraicReeTwist m).onPoints (conjugator m hm))⁻¹ = normalizer m :=
  Classical.choose_spec (algebraicReeTwist_lang (F := F) m hm (normalizer m))

/-- Conjugation places the constructed marked torus in the exceptional fixed subgroup. -/
def fixedMap (m : ℕ) (hm : 1 ≤ m) (f : QuadraticField m →+* F) :
    Parameters m →* algebraicFixed (algebraicReeTwist (F := F) m).onPoints :=
  (((MulAut.conj (conjugator m hm)⁻¹).toMonoidHom).comp (algebraicMap m f)).codRestrict _
    (fun a => by
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        conjugated_fixed _ _ _ _ (conjugator_equation m hm) (algebraicMap_twisted_fixed m f a))

theorem fixedMap_injective (m : ℕ) (hm : 1 ≤ m) (f : QuadraticField m →+* F) :
    Function.Injective (fixedMap m hm f) := by
  intro a b h
  apply algebraicMap_injective m f
  apply (MulAut.conj (conjugator m hm)⁻¹).injective
  exact congrArg Subtype.val h

/-- Both finite fields are transported into this one specified algebraic closure. -/
abbrev Closure (m : ℕ) := AlgebraicClosure (QuadraticField m)

def quadraticEmbedding (m : ℕ) : QuadraticField m →+* Closure m :=
  algebraMap _ _

def coefficientEmbedding (m : ℕ) : CoefficientField m →+* Closure m :=
  coefficientHom (Closure m) m

/-- Finite root-carrier membership is supplied by the proved rational descent. -/
def modelMap (m : ℕ) (hm : 1 ≤ m) : Parameters m →* ReeF4.Model m :=
  (fixedModelEquiv (coefficientEmbedding m)).toMonoidHom.comp
    (fixedMap m hm (quadraticEmbedding m))

theorem modelMap_injective (m : ℕ) (hm : 1 ≤ m) : Function.Injective (modelMap m hm) :=
  (fixedModelEquiv (coefficientEmbedding m)).injective.comp
    (fixedMap_injective m hm (quadraticEmbedding m))

/-- The descended map retains the literal geometric marking, not just its isomorphism type. -/
theorem modelMap_marking (m : ℕ) (hm : 1 ≤ m) (a : Parameters m) :
    Steinberg.modelEmbedding (coefficientEmbedding m) (modelMap m hm a) =
      (conjugator m hm)⁻¹ * algebraicMap m (quadraticEmbedding m) a * conjugator m hm := by
  have h := congrArg Subtype.val
    ((fixedModelEquiv (coefficientEmbedding m)).symm_apply_apply
      (fixedMap m hm (quadraticEmbedding m) a))
  rw [fixedModelEquiv_symm_val] at h
  simpa only [modelMap, fixedMap, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using h

end
end ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus
