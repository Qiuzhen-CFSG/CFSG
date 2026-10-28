module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.Definitions
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.Coordinates
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Marking the seven nontrivial Sylow characters

This interface records a finite character calculation on the actual Sylow
eight. The two possible Singer orientations are kept explicit. The displayed
permutations follow the column-vector convention: `sourceY` sends column i
to i−1, and `normalU` sends column i to 2i+3 modulo seven.

Existence of this marking is a group-theoretic obligation, separate from the
linear-algebra construction of its eigenbasis. The record has no representation
or basis field. Its purpose is the normalization preceding Gorenstein,
*Finite Groups*, §16.6, equations (6.1)–(6.2), pp.482–483.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation

variable {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G}

/-- Retain the allowed inversion of the marked seven-generator. -/
@[expose] public def orientedY (D : NormalizerFrame h) (reverse : Bool) : G :=
  if reverse then D.y⁻¹ else D.y

public theorem orientedY_mem (D : NormalizerFrame h) (reverse : Bool) :
    orientedY D reverse ∈ D.H := by
  cases reverse <;> simp only [orientedY, Bool.false_eq_true, ↓reduceIte]
  · exact D.y_mem
  · exact D.H.inv_mem D.y_mem

/-- Both allowed orientations have seventh power one. -/
public theorem orientedY_pow_seven (D : NormalizerFrame h) (reverse : Bool) :
    orientedY D reverse ^ 7 = 1 := by
  have hy : D.y ^ 7 = 1 := D.order_y ▸ pow_orderOf_eq_one D.y
  cases reverse <;> simp [orientedY, inv_pow, hy]

/-- Inverting y preserves the chosen cubic conjugation relation. -/
public theorem orientedY_action (D : NormalizerFrame h) (reverse : Bool) :
    D.u * orientedY D reverse * D.u⁻¹ = orientedY D reverse ^ 2 := by
  cases reverse
  · exact D.action
  · have hh := congrArg (fun g : G => g⁻¹) D.action
    simpa only [orientedY, ↓reduceIte, mul_inv_rev, inv_inv, inv_pow, mul_assoc] using hh

/-- The direct conjugation action of the oriented seven-generator on S. -/
@[expose] public def sylowY (D : NormalizerFrame h) (reverse : Bool) : MulAut h.sylow :=
  (h.sylow : Subgroup G).normalizerMonoidHom
    ⟨orientedY D reverse, D.H_le (orientedY_mem D reverse)⟩

/-- The direct conjugation action of the marked cubic element on S. -/
@[expose] public def sylowU (D : NormalizerFrame h) : MulAut h.sylow :=
  (h.sylow : Subgroup G).normalizerMonoidHom ⟨D.u, D.H_le D.u_mem⟩

/-- The finite character marking needed by the eigenbasis construction.
All characters and automorphisms are on the literal source Sylow subgroup. -/
public structure NormalizerCharacterFrame (D : NormalizerFrame h) where
  reverse : Bool
  character : Fin 7 → (h.sylow →* (ZMod 11)ˣ)
  injective : Function.Injective character
  nontrivial : ∀ i, character i ≠ 1
  exhaustive : ∀ χ : h.sylow →* (ZMod 11)ˣ, χ ≠ 1 → ∃ i, character i = χ
  y_action : ∀ i s, character (i - 1) s = character i ((sylowY D reverse).symm s)
  u_action : ∀ i s, character (2 * i + 3) s = character i ((sylowU D).symm s)
  x_value : ∀ i, (character i ⟨D.x, D.x_mem⟩ : ZMod 11) = normalX i i

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation
