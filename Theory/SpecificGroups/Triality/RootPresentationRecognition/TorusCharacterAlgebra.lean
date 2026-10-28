module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.TorusRelations

/-!
# Algebra of the folded torus characters

The source and model torus consumers use the same cubic norm and the same
three short and three long characters.  This file records their elementary
unit-group algebra independently of any group presentation or model map.  In
particular, the norm and every folded character are multiplicative for the
actual extension field and its Frobenius-fixed subfield.  The statements keep
the original extension/fixed-field codomains, so they can be used directly by
source Cartan calculations.
-/

@[expose] public noncomputable section
namespace Triality.Standard.RootPresentationRecognition
open Parabolics ConcreteBruhat.TorusCoordinates
variable {n : ℕ} {hn : 0 < n}
local notation "P" => binaryParameters n hn

@[simp] theorem normUnit_one : normUnit (1 : (ExtensionField P)ˣ) = 1 := by
  apply Units.ext
  apply Subtype.ext
  simp [normUnit, restrictUnit]

theorem normUnit_mul (s t : (ExtensionField P)ˣ) :
    normUnit (s * t) = normUnit s * normUnit t := by
  apply Units.ext
  apply Subtype.ext
  simp only [normUnit, restrictUnit, Units.val_mul, map_mul]
  change (s.val * t.val) * (fieldFrobenius P s.val * fieldFrobenius P t.val) *
      (fieldFrobenius P (fieldFrobenius P s.val) *
        fieldFrobenius P (fieldFrobenius P t.val)) =
    (s.val * fieldFrobenius P s.val * fieldFrobenius P (fieldFrobenius P s.val)) *
      (t.val * fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val))
  ring

theorem shortCharacter_mul (p q : TorusParameters n hn) (i : Fin 3) :
    shortCharacter (p * q) i = shortCharacter p i * shortCharacter q i := by
  fin_cases i <;> apply Units.ext <;>
    simp [shortCharacter, mul_pow, map_mul, div_eq_mul_inv] <;>
    ring

theorem longCharacter_mul (p q : TorusParameters n hn) (i : Fin 3) :
    longCharacter (p * q) i = longCharacter p i * longCharacter q i := by
  fin_cases i <;> apply Units.ext <;>
    simp [longCharacter, normUnit_mul, mul_pow, div_eq_mul_inv] <;>
    ring

theorem normUnit_inv (t : (ExtensionField P)ˣ) :
    normUnit t⁻¹ = (normUnit t)⁻¹ := by
  have hi : Function.Injective (fixedUnit P) := fun a b h =>
    Units.ext (Subtype.ext (congrArg Units.val h))
  apply hi
  simp only [normUnit, fixedUnit_restrictUnit, map_inv]
  simp only [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

theorem shortCharacter_inv (p : TorusParameters n hn) (i : Fin 3) :
    shortCharacter p⁻¹ i = (shortCharacter p i)⁻¹ := by
  fin_cases i <;> simp [shortCharacter] <;>
    apply Additive.ofMul.injective <;>
    simp only [ofMul_mul, ofMul_div, ofMul_inv] <;>
    abel

theorem longCharacter_inv (p : TorusParameters n hn) (i : Fin 3) :
    longCharacter p⁻¹ i = (longCharacter p i)⁻¹ := by
  fin_cases i <;> simp [longCharacter, normUnit_inv] <;>
    apply Additive.ofMul.injective <;>
    simp only [ofMul_mul, ofMul_div, ofMul_inv] <;>
    abel

namespace SignedRoots
variable {Y : Type*} [Group Y]
  (L : SignedRoots (n := n) (hn := hn) Y)

/-- The torus word is multiplicative once the two rank-one factors commute.
The only group input is the displayed cross-commutation; all scalar
characters are handled separately by the source Cartan calculation. -/
theorem torus_mul_of_commute
    (hA : ∀ s t, L.hA (s * t) = L.hA s * L.hA t)
    (hB : ∀ s t, L.hB (s * t) = L.hB s * L.hB t)
    (hcomm : ∀ s t, Commute (L.hA s) (L.hB t))
    (p q : TorusParameters n hn) :
    L.torus (p * q) = L.torus p * L.torus q := by
  change L.hA (p.1 * q.1) * L.hB (p.2 * q.2) =
    (L.hA p.1 * L.hB p.2) * (L.hA q.1 * L.hB q.2)
  rw [hA, hB]
  calc
    _ = L.hA p.1 * (L.hA q.1 * L.hB p.2) * L.hB q.2 := by group
    _ = L.hA p.1 * (L.hB p.2 * L.hA q.1) * L.hB q.2 := by
      rw [(hcomm q.1 p.2).eq]
    _ = (L.hA p.1 * L.hB p.2) * (L.hA q.1 * L.hB q.2) := by group

end SignedRoots

@[simp] theorem shortCharacter_one (i : Fin 3) :
    shortCharacter (1 : TorusParameters n hn) i = 1 := by
  fin_cases i <;> simp [shortCharacter]

@[simp] theorem longCharacter_one (i : Fin 3) :
    longCharacter (1 : TorusParameters n hn) i = 1 := by
  fin_cases i <;> simp [longCharacter, normUnit_one]

end Triality.Standard.RootPresentationRecognition
