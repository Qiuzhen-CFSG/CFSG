module
public import CFSG.Quasithin.ChapterD.Section01.Configuration
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.BinaryOffender.Defs

/-!
# The original internal-module ratio in D.1

The acting group is the actual conjugation image G₁/C_G₁(V) specified in
QRCConfiguration. Its tautological action on Additive V is faithful. This
fixes a source-level ratio for the conjugate-generator transport in D.1.3;
it is not a real-valued proxy, and may initially equal infinity.

Source: Aschbacher--Smith, Hypothesis D.1.1 and Proposition D.1.3,
printed pp.171--175; quadratic ratio is Definition B.1.1, printed p.67.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.MultipleFactors
open scoped IsMulCommutative ENNReal
open Representation.BinaryOffender
variable {G : Type*} [Group G] (H V : Subgroup G)
  (hn : H ≤ Subgroup.normalizer (V : Set G)) [IsElementaryAbelian 2 V]

/-- The source faithful binary representation of the literal internal action image. -/
noncomputable def internalRepresentation :
    Representation (ZMod 2) (internalActionImage H V hn) (Additive V) where
  toFun a := a.val.toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    rfl

/-- This is the actual extended B.1 quadratic ratio, including its infinite case. -/
noncomputable def internalQuadraticRatio : ℝ≥0∞ :=
  quadraticRatio (internalRepresentation H V hn)

/-- Tautological faithfulness on G₁/C_G₁(V). -/
theorem internalRepresentation_injective : Function.Injective (internalRepresentation H V hn) := by
  intro a b hab
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  exact congrArg Additive.toMul (LinearMap.congr_fun hab (Additive.ofMul v))

/-- Elements of the image act by the original ambient conjugation formula. -/
theorem internalRepresentation_apply (h : H) (v : Additive V) :
    ((internalRepresentation H V hn
      ((V.normalizerMonoidHom.comp (Subgroup.inclusion hn)).rangeRestrict h) v).toMul : G) =
      (h : G) * v.toMul * (h : G)⁻¹ := rfl

/-- The image has the finite group structure supplied by the original finite local subgroup. -/
instance [Finite H] : Finite (internalActionImage H V hn) :=
  Finite.of_surjective _ (V.normalizerMonoidHom.comp (Subgroup.inclusion hn)).rangeRestrict_surjective

end CFSG.Quasithin.ChapterD.MultipleFactors
