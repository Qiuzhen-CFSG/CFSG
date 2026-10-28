module

public import Theory.Representation.NonsplitFour
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Small faithful-degree exclusions for the Hall--Janko carrier

The certified order 604800 contains a factor 25. The orders of GL(n,2) for
n ≤ 6 and GL(n,4) for n ≤ 3 do not. A faithful representation embeds the
actual group in the corresponding general linear group, so Lagrange's theorem
excludes those degrees. The products are checked using the uniform GL order
formula, without enumerating any matrices.

These are the degree obstructions used for the natural restriction in
Aschbacher--Smith, K.4.5, printed p.460. The imported J₂ permutation order
certificate retains its ATLAS attribution and license.
-/

public section

namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.BinaryIrreducibility
open Matrix

/-- A faithful binary action of J₂ cannot have dimension at most six. -/
theorem not_injective_binary_of_finrank_le_six {U : Type*}
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Carrier U) (hd : Module.finrank (ZMod 2) U ≤ 6) :
    ¬ Function.Injective ρ := by
  intro hρ
  have h := Representation.card_dvd_card_GL_of_injective ρ hρ
  rw [ExceptionalParabolics.FirstParabolic.card_carrier, card_GL_field] at h
  interval_cases hn : Module.finrank (ZMod 2) U <;>
    norm_num [Fin.prod_univ_succ] at h

/-- A faithful action over F₄ cannot have dimension at most three. -/
theorem not_injective_four_of_finrank_le_three {U : Type*}
    [AddCommGroup U] [Module (GaloisField 2 2) U] [FiniteDimensional (GaloisField 2 2) U]
    (ρ : Representation (GaloisField 2 2) Carrier U)
    (hd : Module.finrank (GaloisField 2 2) U ≤ 3) : ¬ Function.Injective ρ := by
  let := Fintype.ofFinite (GaloisField 2 2)
  intro hρ
  have h := Representation.card_dvd_card_GL_of_injective ρ hρ
  rw [ExceptionalParabolics.FirstParabolic.card_carrier, card_GL_field,
    ← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)] at h
  interval_cases hn : Module.finrank (GaloisField 2 2) U <;>
    norm_num [Fin.prod_univ_succ] at h

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.BinaryIrreducibility
