module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.Actions
public import Mathlib.GroupTheory.Sylow

/-!
# Coordinates for the binary S₄ action classification

Action equivalence transports fixed spaces and faithfulness without changing
actor labels. The permutations `(0 1 2)`, `(0 1)`, and `(0 1)(2 3)` generate
S₄: a kernel-checked list gives the V₄-by-S₃ normal form. Thus intertwining
these three permutations is sufficient to intertwine the whole action.
Binary automorphisms are likewise determined by the four coordinate vectors.

These elementary coordinate reductions support the independent finite action
classification used for Huppert–Blackburn, *Finite Groups III*, XII.1.18(b),
p.314. They do not assert completeness of the four proposed action models.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
open LocalModelDichotomy

namespace ActionEquivalent

/-- Every action is equivalent to itself. -/
public theorem refl (α : SymmetricFour →* MulAut BinaryFour) : ActionEquivalent α α :=
  ⟨MulEquiv.refl _, fun _ _ => rfl⟩

/-- Inverting the basis change reverses action equivalence. -/
public theorem symm {α β : SymmetricFour →* MulAut BinaryFour}
    (h : ActionEquivalent α β) : ActionEquivalent β α := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun s v => ?_⟩
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

/-- Composing basis changes composes action equivalences. -/
public theorem trans {α β γ : SymmetricFour →* MulAut BinaryFour}
    (hab : ActionEquivalent α β) (hbc : ActionEquivalent β γ) : ActionEquivalent α γ := by
  obtain ⟨e, he⟩ := hab
  obtain ⟨f, hf⟩ := hbc
  refine ⟨e.trans f, fun s v => ?_⟩
  change f (e (α s v)) = γ s (f (e v))
  rw [he, hf]

/-- Equivalence preserves fixed-point cardinalities for any family of actors. -/
public theorem fixed_card_eq {α β : SymmetricFour →* MulAut BinaryFour}
    (h : ActionEquivalent α β) {S : Type*} (f : S → SymmetricFour) :
    Nat.card {v : BinaryFour // ∀ s : S, α (f s) v = v} =
      Nat.card {v : BinaryFour // ∀ s : S, β (f s) v = v} := by
  obtain ⟨e, he⟩ := h
  apply Nat.card_congr
  exact {
    toFun := fun v => ⟨e v, fun s => (he (f s) v).symm.trans (congrArg e (v.2 s))⟩
    invFun := fun v => ⟨e.symm v, fun s => e.injective (by
      rw [he, e.apply_symm_apply, v.2 s])⟩
    left_inv := fun v => Subtype.ext (e.symm_apply_apply v)
    right_inv := fun v => Subtype.ext (e.apply_symm_apply v) }

/-- Equivalence preserves faithfulness. -/
public theorem injective {α β : SymmetricFour →* MulAut BinaryFour}
    (h : ActionEquivalent α β) (hα : Function.Injective α) : Function.Injective β := by
  obtain ⟨e, he⟩ := h
  intro s t hst
  apply hα
  apply MulEquiv.ext
  intro v
  apply e.injective
  rw [he, he, hst]

end ActionEquivalent

namespace ActionClassification

/-- The labelled three-cycle `(0 1 2)`. -/
@[expose] public def threeCycle : SymmetricFour := Equiv.swap 0 1 * Equiv.swap 1 2
/-- The labelled transposition `(0 1)`. -/
@[expose] public def transposition : SymmetricFour := Equiv.swap 0 1
/-- The labelled double transposition `(0 1)(2 3)`. -/
@[expose] public def doubleTransposition : SymmetricFour := Equiv.swap 0 1 * Equiv.swap 2 3

/-- Conjugate the action by an actual multiplicative basis change. -/
@[expose] public def changeBasis (α : SymmetricFour →* MulAut BinaryFour)
    (e : MulAut BinaryFour) : SymmetricFour →* MulAut BinaryFour :=
  (MulAut.congr e).toMonoidHom.comp α

public theorem changeBasis_apply (α : SymmetricFour →* MulAut BinaryFour)
    (e : MulAut BinaryFour) (s : SymmetricFour) (v : BinaryFour) :
    changeBasis α e s v = e (α s (e.symm v)) := rfl

public theorem equivalent_changeBasis (α : SymmetricFour →* MulAut BinaryFour)
    (e : MulAut BinaryFour) : ActionEquivalent α (changeBasis α e) := by
  refine ⟨e, fun s v => ?_⟩
  rw [changeBasis_apply, e.symm_apply_apply]

public theorem threeCycle_cube : threeCycle ^ 3 = 1 := by decide +kernel

public theorem transposition_square : transposition ^ 2 = 1 := by decide +kernel

public theorem transposition_inverts :
    transposition * threeCycle * transposition = threeCycle⁻¹ := by decide +kernel

public theorem doubleTransposition_square : doubleTransposition ^ 2 = 1 := by decide +kernel

public theorem transposition_commutes_double :
    transposition * doubleTransposition = doubleTransposition * transposition := by decide +kernel

public theorem threeCycle_ne_one : threeCycle ≠ 1 := by decide +kernel

private def normalWord (i : Fin 4) : SymmetricFour :=
  if i = 0 then 1 else if i = 1 then doubleTransposition
  else if i = 2 then threeCycle * doubleTransposition * threeCycle⁻¹
  else threeCycle⁻¹ * doubleTransposition * threeCycle

private theorem word_exhaustive : ∀ s : SymmetricFour,
    ∃ (i : Fin 4) (j : Fin 3) (k : Fin 2),
      s = normalWord i * threeCycle ^ j.val * transposition ^ k.val := by decide +kernel

/-- A homomorphism from S₄ is determined by these three labelled generators. -/
public theorem hom_ext {H : Type*} [Group H] (α β : SymmetricFour →* H)
    (hthree : α threeCycle = β threeCycle)
    (htwo : α transposition = β transposition)
    (hdouble : α doubleTransposition = β doubleTransposition) : α = β := by
  apply MonoidHom.ext
  intro s
  obtain ⟨i, j, k, rfl⟩ := word_exhaustive s
  simp only [map_mul, map_pow]
  have hword : α (normalWord i) = β (normalWord i) := by
    simp only [normalWord]
    split_ifs <;> simp [hthree, hdouble]
  rw [hword, hthree, htwo]


/-- A standard coordinate vector, in multiplicative notation. -/
@[expose] public def binaryBasis (i : Fin 4) : BinaryFour := Multiplicative.ofAdd (Pi.single i 1)

open scoped BigOperators

/-- The four binary coordinate vectors generate the elementary group. -/
public theorem binaryBasis_expansion (v : BinaryFour) :
    v = ∏ i : Fin 4, binaryBasis i ^ (v.toAdd i).val := by
  have h : ∀ v : BinaryFour, v = ∏ i : Fin 4, binaryBasis i ^ (v.toAdd i).val := by
    decide +kernel
  exact h v

/-- Binary automorphisms agreeing on the coordinate vectors are equal. -/
public theorem mulAut_ext (e f : MulAut BinaryFour)
    (h : ∀ i : Fin 4, e (binaryBasis i) = f (binaryBasis i)) : e = f := by
  apply MulEquiv.ext
  intro v
  conv_lhs => rw [binaryBasis_expansion v]
  conv_rhs => rw [binaryBasis_expansion v]
  simp only [map_prod, map_pow, h]

/-- A multiplicative change of basis intertwining the generators intertwines S₄. -/
public theorem equivalent_of_generators
    (α β : SymmetricFour →* MulAut BinaryFour) (e : MulAut BinaryFour)
    (hthree : ∀ v, e (α threeCycle v) = β threeCycle (e v))
    (htwo : ∀ v, e (α transposition v) = β transposition (e v))
    (hdouble : ∀ v, e (α doubleTransposition v) = β doubleTransposition (e v)) :
    ActionEquivalent α β := by
  have heq : changeBasis α e = β := by
    apply hom_ext
    · apply MulEquiv.ext
      intro v
      rw [changeBasis_apply, hthree, e.apply_symm_apply]
    · apply MulEquiv.ext
      intro v
      rw [changeBasis_apply, htwo, e.apply_symm_apply]
    · apply MulEquiv.ext
      intro v
      rw [changeBasis_apply, hdouble, e.apply_symm_apply]
  rw [← heq]
  exact equivalent_changeBasis α e

end ActionClassification
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
