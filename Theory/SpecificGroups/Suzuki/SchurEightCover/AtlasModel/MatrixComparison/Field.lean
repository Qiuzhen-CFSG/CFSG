module

public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Algebra.CharP.CharAndCard
public import BenderSuzuki.MatrixGroups.Suzuki

/-!
# Explicit binary field for the Suzuki matrix comparison

The field is binary polynomial arithmetic modulo X³ + X + 1. Its eight
values and field laws are checked in the kernel. The element `v` represents
X; `code` uses the convention 0, 1, v, v², ..., v⁶ of the saved ATLAS
comparison witnesses. Equality of field cardinalities supplies the actual
transport to the native `BinaryGaloisField 3`.

The arithmetic construction follows the private HeringF8 implementation in
`BenderSuzuki/SE/II1Hering31Finite.lean`, with an explicit computable inverse.
Source context: Aschbacher–Smith I.1.1 and I.1.3(5), printed p.407.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison

structure F8 where
  c0 : Bool
  c1 : Bool
  c2 : Bool
deriving DecidableEq

instance : Fintype F8 where
  elems := {
    ⟨false, false, false⟩, ⟨true, false, false⟩,
    ⟨false, true, false⟩, ⟨true, true, false⟩,
    ⟨false, false, true⟩, ⟨true, false, true⟩,
    ⟨false, true, true⟩, ⟨true, true, true⟩ }
  complete := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp

instance decidableForallF8 (p : F8 → Prop)
    [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff
    (p ⟨false, false, false⟩ ∧ p ⟨true, false, false⟩ ∧
      p ⟨false, true, false⟩ ∧ p ⟨true, true, false⟩ ∧
      p ⟨false, false, true⟩ ∧ p ⟨true, false, true⟩ ∧
      p ⟨false, true, true⟩ ∧ p ⟨true, true, true⟩) (by
        constructor
        · rintro ⟨h000, h100, h010, h110, h001, h101, h011, h111⟩
          rintro ⟨a, b, c⟩
          fin_cases a <;> fin_cases b <;> fin_cases c <;> assumption
        · intro h
          exact ⟨h _, h _, h _, h _, h _, h _, h _, h _⟩)

instance : Zero F8 :=
  ⟨⟨false, false, false⟩⟩

instance : One F8 :=
  ⟨⟨true, false, false⟩⟩

instance : Add F8 :=
  ⟨fun a b => ⟨a.c0 ^^ b.c0, a.c1 ^^ b.c1, a.c2 ^^ b.c2⟩⟩

instance : Neg F8 :=
  ⟨fun a => a⟩

instance : Mul F8 :=
  ⟨fun a b =>
    ⟨(a.c0 && b.c0) ^^ (a.c1 && b.c2) ^^ (a.c2 && b.c1),
      (a.c0 && b.c1) ^^ (a.c1 && b.c0) ^^ (a.c1 && b.c2) ^^
        (a.c2 && b.c1) ^^ (a.c2 && b.c2),
      (a.c0 && b.c2) ^^ (a.c1 && b.c1) ^^ (a.c2 && b.c0) ^^
        (a.c2 && b.c2)⟩⟩


instance : Inv F8 := ⟨fun a => (a * a) * ((a * a) * (a * a))⟩

instance : Field F8 :=
  Field.ofMinimalAxioms F8
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ⟨0, 1, by decide⟩

instance : CharP F8 2 :=
  charP_of_card_eq_prime_pow (show Fintype.card F8 = 2 ^ 3 by decide)

theorem card_F8 : Fintype.card F8 = 8 := by decide

def v : F8 := ⟨false, true, false⟩

theorem v_seventh : v ^ 7 = 1 := by decide +kernel

theorem v_cubic : v ^ 3 = v + 1 := by decide +kernel

def vUnit : F8ˣ := Units.mk0 v (by decide)

/-- The external field codes denote powers, not natural-number casts. -/
def code (n : Fin 8) : F8 :=
  ![0, 1, v, v ^ 2, v ^ 3, v ^ 4, v ^ 5, v ^ 6] n

theorem code_bijective : Function.Bijective code := by decide +kernel

noncomputable def fieldEquiv : F8 ≃+* PFAppendixIII.BinaryGaloisField 3 := by
  letI : Fintype (PFAppendixIII.BinaryGaloisField 3) := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [card_F8, ← Nat.card_eq_fintype_card]
    symm
    simpa [PFAppendixIII.BinaryGaloisField] using
      (GaloisField.card 2 3 (by omega)))

abbrev Mat := Matrix (Fin 4) (Fin 4) F8
abbrev GL8 := Matrix.GeneralLinearGroup (Fin 4) F8
abbrev NativeGL := Matrix.GeneralLinearGroup (Fin 4) (PFAppendixIII.BinaryGaloisField 3)

/-- Entrywise transport preserves ordinary matrix multiplication. -/
noncomputable def glEquiv : GL8 ≃* NativeGL :=
  Units.mapEquiv fieldEquiv.mapMatrix.toMulEquiv

@[simp] theorem glEquiv_apply (g : GL8) (i j : Fin 4) :
    glEquiv g i j = fieldEquiv (g i j) := rfl

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison
