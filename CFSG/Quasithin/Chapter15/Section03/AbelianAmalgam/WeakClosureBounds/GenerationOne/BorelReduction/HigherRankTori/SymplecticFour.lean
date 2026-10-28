module

public import Theory.SpecificGroups.SymplecticFour.Sylow.Characters
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.CharP.Two
public import Mathlib.FieldTheory.Finite.Basic

/-!
# A split torus in Sp₄ and in its derived subgroup

The diagonal matrices diag(a, 1, a⁻¹, 1) lie in the actual symplectic flag
stabilizer. The symplectic matrix J inverts this torus, so the commutator
of a torus element with J is its square. Every element of a finite field
of characteristic two is a square; consequently this entire torus lies
in Sp₄(F)′. Restricting the flag stabilizer to that derived subgroup gives
the required injection for the source convention, without a perfectness
assumption or an identification of Sp₄(2)′ with Sp₄(2).

Source: Aschbacher–Smith, E.2.2(2b), printed pp.215–216, and 15.3.65,
printed p.1152 (`refs/quasithin.pdf`, combined manuscript of 1 March 2004).
-/

@[expose] public section

open Matrix Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement
noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
variable {F : Type*} [Field F]

/-- The first-coordinate diagonal torus in the concrete Sp₄ flag stabilizer. -/
def sp4Torus : Fˣ →* borel (F := F) where
  toFun a := ⟨diagonalTorus a 1, diagonalTorus_mem_borel a 1⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [diagonalTorus, diagonal]
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [mul_comm]

/-- Its first diagonal entry recovers the unit. -/
theorem sp4Torus_injective : Function.Injective (sp4Torus (F := F)) := by
  intro a b h
  apply Units.ext
  exact congrArg (fun x : borel (F := F) => x.val.val (.inl 0) (.inl 0)) h

private def tor : Fˣ →* Sp F := (borel (F := F)).subtype.comp sp4Torus

private theorem weyl_intertwine (a : Fˣ) :
    SymplecticGroup.symJ (Fin 2) F * tor a = tor a⁻¹ * SymplecticGroup.symJ (Fin 2) F := by
  apply Subtype.ext
  change J _ _ * diagonal _ = diagonal _ * J _ _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.J, Matrix.fromBlocks]

private theorem tor_square_commutator (a : Fˣ) :
    ⁅tor a, SymplecticGroup.symJ (Fin 2) F⁆ = tor (a * a) := by
  calc
    ⁅tor a, SymplecticGroup.symJ (Fin 2) F⁆ =
        tor a * (SymplecticGroup.symJ (Fin 2) F * tor a⁻¹) *
          (SymplecticGroup.symJ (Fin 2) F)⁻¹ := by
      simp only [commutatorElement_def, map_inv, mul_assoc]
    _ = tor a * (tor a * SymplecticGroup.symJ (Fin 2) F) *
          (SymplecticGroup.symJ (Fin 2) F)⁻¹ := by rw [weyl_intertwine, inv_inv]
    _ = tor (a * a) := by simp [map_mul, mul_assoc]

/-- The source torus lies in Sp₄(F)′, including the binary exceptional case. -/
theorem sp4Torus_mem_derived [Finite F] [CharP F 2] (a : Fˣ) :
    diagonalTorus a 1 ∈ commutator (Sp F) := by
  obtain ⟨b, hb⟩ := isSquare_of_charTwo' (a : F)
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hb
  let u := Units.mk0 b hb0
  have hu : a = u * u := Units.ext hb
  change tor a ∈ commutator (Sp F)
  rw [hu, ← tor_square_commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The literal flag stabilizer inside the derived symplectic group. -/
abbrev sp4DerivedBorel : Subgroup (commutator (Sp F)) :=
  (borel (F := F)).comap (commutator (Sp F)).subtype

/-- The same torus, restricted to the source derived-group Borel. -/
def sp4DerivedTorus [Finite F] [CharP F 2] : Fˣ →* sp4DerivedBorel (F := F) :=
  (((borel (F := F)).subtype.comp sp4Torus).codRestrict _
    (sp4Torus_mem_derived (F := F))).codRestrict _
    (fun a => diagonalTorus_mem_borel a 1)

/-- Restriction to the derived subgroup preserves injectivity. -/
theorem sp4DerivedTorus_injective [Finite F] [CharP F 2] :
    Function.Injective (sp4DerivedTorus (F := F)) := by
  intro a b h
  apply Units.ext
  exact congrArg (fun x : sp4DerivedBorel (F := F) => x.val.val.val (.inl 0) (.inl 0)) h
/-- The field-order hypothesis alone supplies characteristic two and the
required injection; in particular this applies to every source exponent f > 1. -/
theorem exists_sp4DerivedTorus_of_card [Finite F] {f : ℕ} (hf : 0 < f)
    (hcard : Nat.card F = 2 ^ f) :
    ∃ t : Fˣ →* sp4DerivedBorel (F := F), Function.Injective t := by
  let : Fintype F := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : f ≠ 0)))
  let : CharP F 2 := ringChar.of_eq hc
  exact ⟨sp4DerivedTorus, sp4DerivedTorus_injective⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
