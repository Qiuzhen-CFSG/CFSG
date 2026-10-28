module
public import Theory.GroupTheory.ClassTwoCentralPairing
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The ternary commutator form with its original center coordinate

A center isomorphism to the multiplicative ternary field converts the actual
commutator pairing into a bilinear form on the additive central quotient.
Alternation, nondegeneracy and automorphism naturality preserve the original
quotient map and center elements. This supplies the literal form input for
the marked complement classifier in Aschbacher (1994), 45.11, p.248.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory.CentralQuotient
variable {D : Type*} [Group D] [IsElementaryAbelian 3 (D ⧸ center D)]

private def pairingAdd (eZ : center D ≃* Multiplicative (ZMod 3)) :
    Additive (D ⧸ center D) →+ (Additive (D ⧸ center D) →+ ZMod 3) where
  toFun x := (eZ.toMonoidHom.comp (pairing x.toMul)).toAdditiveLeft
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    change (eZ (pairing 1 y.toMul)).toAdd=0
    rw [map_one,MonoidHom.one_apply,map_one]
    rfl
  map_add' x y := by
    apply AddMonoidHom.ext
    intro v
    change (eZ (pairing (x.toMul*y.toMul) v.toMul)).toAdd =
      (eZ (pairing x.toMul v.toMul)).toAdd+(eZ (pairing y.toMul v.toMul)).toAdd
    rw [map_mul,MonoidHom.mul_apply,map_mul]
    rfl

/-- The literal commutator pairing as a ternary bilinear form. -/
def pairingForm (eZ : center D ≃* Multiplicative (ZMod 3)) :
    LinearMap.BilinForm (ZMod 3) (Additive (D ⧸ center D)) :=
  ((AddMonoidHom.toZModLinearMapEquiv 3).toAddMonoidHom.comp (pairingAdd eZ)).toZModLinearMap 3

@[simp] theorem pairingForm_apply (eZ : center D ≃* Multiplicative (ZMod 3))
    (x y : Additive (D ⧸ center D)) :
    pairingForm eZ x y=(eZ (pairing x.toMul y.toMul)).toAdd := by rfl

theorem pairingForm_isAlt (eZ : center D ≃* Multiplicative (ZMod 3)) :
    (pairingForm eZ).IsAlt := by
  intro x
  rw [pairingForm_apply,pairing_self,map_one]
  rfl

theorem pairingForm_nondegenerate (eZ : center D ≃* Multiplicative (ZMod 3))
    (x : Additive (D ⧸ center D)) (hx : ∀ y, pairingForm eZ x y=0) : x=0 := by
  apply Additive.toMul.injective
  apply pairing_nondegenerate
  intro y
  apply eZ.injective
  have hh := congrArg Multiplicative.ofAdd (hx (Additive.ofMul y))
  exact hh.trans eZ.map_one.symm

/-- Naturality retains the original quotient automorphism and original center map. -/
theorem pairing_quotientAut (g : MulAut D) (x y : D ⧸ center D) :
    (pairing (quotientAut (center D) g x) (quotientAut (center D) g y) : D) =
      g (pairing x y) := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center D) x
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (center D) y
  rw [quotientAut_apply_mk,quotientAut_apply_mk,pairing_mk_mk,pairing_mk_mk,map_commutatorElement]

end Theory.GroupTheory.CentralQuotient
