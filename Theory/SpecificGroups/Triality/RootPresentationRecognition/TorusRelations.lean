module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.WeylAction
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.Coordinates

/-!
# The explicit signed triality torus relations

The torus is defined by the signed simple-root words on units of the actual
cubic field and its Frobenius fixed subfield. Its six characters retain the
original orbit origins and all Frobenius shifts. Multiplicativity and the
signed root and Weyl conjugation laws are equations in the unknown group;
no homomorphism to a model, order, or faithfulness is assumed.

These equations complete the map-free contract for the abstract Bruhat
collector. Their concrete model verification and their reconstruction in a
source quotient are separate mathematical obligations.
Source: GLS3 2.4.7–8, with the orbit convention of `FoldedRoots.lean`.
-/

@[expose] public noncomputable section
namespace Triality.Standard.RootPresentationRecognition
open Parabolics ConcreteBruhat.TorusCoordinates
variable {n : ℕ} {hn : 0 < n}
local notation "P" => binaryParameters n hn

abbrev TorusParameters (n : ℕ) (hn : 0 < n) :=
  (ExtensionField (binaryParameters n hn))ˣ × (fixedField (binaryParameters n hn))ˣ

/-- The norm of a cubic-field unit, in the actual fixed subfield. -/
def normUnit (t : (ExtensionField P)ˣ) : (fixedField P)ˣ :=
  restrictUnit P (t * frobenius P t * frobenius P (frobenius P t)) (by
    simp only [map_mul, frobenius_three]
    ac_rfl)

/-- Characters on A, C, D in the original folded orbit marking. -/
def shortCharacter (p : TorusParameters n hn) : Fin 3 → (ExtensionField P)ˣ :=
  ![p.1 ^ 2 / fixedUnit P p.2,
    p.1 * fixedUnit P p.2 / (frobenius P p.1 * frobenius P (frobenius P p.1)),
    p.1 * frobenius P p.1 / frobenius P (frobenius P p.1)]

/-- Characters on B, E, F, retaining their fixed-field codomain. -/
def longCharacter (p : TorusParameters n hn) : Fin 3 → (fixedField P)ˣ :=
  ![p.2 ^ 2 / normUnit p.1, normUnit p.1 / p.2, p.2]

namespace SignedRoots
variable {Y : Type*} [Group Y] (L : SignedRoots (n := n) (hn := hn) Y)

def torus (p : TorusParameters n hn) : Y := L.hA p.1 * L.hB p.2

/-- Explicit torus equations. All torus elements are defined root words. -/
structure TorusRelations : Prop where
  mul : ∀ p q, L.torus (p*q) = L.torus p * L.torus q
  short : ∀ p s i t, L.torus p * L.shortSigned s i t * (L.torus p)⁻¹ =
    L.shortSigned s i ((if s then (shortCharacter p i).val else
      ((shortCharacter p i)⁻¹).val) * t)
  long : ∀ p s i t, L.torus p * L.longSigned s i t * (L.torus p)⁻¹ =
    L.longSigned s i ((if s then (longCharacter p i).val else
      ((longCharacter p i)⁻¹).val) * t)
  arms : ∀ p, L.nA 1 * L.torus p * (L.nA 1)⁻¹ =
    L.torus (fixedUnit P p.2 / p.1, p.2)
  central : ∀ p, L.nB 1 * L.torus p * (L.nB 1)⁻¹ =
    L.torus (p.1, normUnit p.1 / p.2)

/-- The complete map-free relation contract. -/
structure Relations : Prop extends WeylRelations L, ActionRelations L, TorusRelations L

variable (R : L.Relations)

def torusHom : TorusParameters n hn →* Y :=
  MonoidHom.mk' L.torus R.mul

@[simp] theorem torusHom_apply (p : TorusParameters n hn) : L.torusHom R p = L.torus p := rfl

def borel : Subgroup Y := L.positive.positiveClosure ⊔ (L.torusHom R).range

def reflection (a : Bool) : Y := if a then L.nA 1 else L.nB 1

def simpleValue (a : Bool) (v : PositiveParameters n hn) : Y :=
  if a then L.shortValue 0 (v.1 0) else L.longValue 0 (v.2 0)

include R in
theorem reflection_inv (a : Bool) : (L.reflection a)⁻¹ = L.reflection a := by
  apply inv_eq_of_mul_eq_one_left
  cases a
  · exact (pow_two _).symm.trans R.nB_sq
  · exact (pow_two _).symm.trans R.nA_sq

include R in
theorem reflection_sq (a : Bool) : L.reflection a * L.reflection a = 1 := by
  calc
    _ = (L.reflection a)⁻¹ * L.reflection a := by rw [L.reflection_inv R a]
    _ = 1 := inv_mul_cancel _

/-- Coordinates after torus conjugation; only multiplication in the original fields is used. -/
def scale (p : TorusParameters n hn) (v : PositiveParameters n hn) : PositiveParameters n hn :=
  (fun i => (shortCharacter p i).val * v.1 i,
   fun i => (longCharacter p i).val * v.2 i)

include R in
theorem torus_factor (p : TorusParameters n hn) (i : Fin 6) (v : PositiveParameters n hn) :
    L.torus p * L.positive.factor i v * (L.torus p)⁻¹ = L.positive.factor i (scale p v) := by
  have hs := R.short p true
  have hl := R.long p true
  simp only [shortSigned, longSigned, if_true] at hs hl
  fin_cases i <;> first | exact hs _ _ | exact hl _ _

include R in
theorem torus_product (p : TorusParameters n hn) (v : PositiveParameters n hn) :
    L.torus p * L.positive.product v * (L.torus p)⁻¹ = L.positive.product (scale p v) := by
  change (MulAut.conj (L.torus p)) (L.positive.product v) = _
  simp only [PositiveRoots.product, map_list_prod, List.map_ofFn, Function.comp_def,
    MulAut.conj_apply, L.torus_factor R]

end SignedRoots
end Triality.Standard.RootPresentationRecognition
