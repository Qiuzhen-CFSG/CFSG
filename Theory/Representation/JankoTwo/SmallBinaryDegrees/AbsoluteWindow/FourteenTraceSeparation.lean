module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.Descent
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveLocal

/-!
# Reduction of the degree-fourteen Hall--Janko trace problem

Binary traces would produce a faithful absolutely irreducible model on F₂¹⁴.
Consequently excluding precisely such binary models suffices over every finite
characteristic-two field and in every universe. Conversely, the nonbinary trace
statement excludes them, since every element of F₂ is fixed by squaring.

The binary exclusion below is an unproved contract. These reduction theorems
do not prove `FourteenTraceSeparation`; no modular representation catalogue or
field-of-definition claim is assumed as an instance. A faithful binary model
without absolute irreducibility is not excluded by this contract.

Sources: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript p.16, and the corrected Hiss--Malle Table 2, degree-14 J₂ entry.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
open Sporadic.LeechRelated.J2
universe v

/-- The still-unproved obstruction on standard binary coordinates. -/
@[expose] def BinaryFourteenExclusion : Prop :=
  ∀ σ : Representation (ZMod 2) Carrier (Fin 14 → ZMod 2),
    Function.Injective σ → ¬ σ.IsAbsolutelyIrreducible

/-- A binary obstruction supplies the nonbinary trace witness in every finite
characteristic-two field, with no representation catalogue as an extra input. -/
theorem fourteenTraceSeparation_of_binaryExclusion (h : BinaryFourteenExclusion) :
    FourteenTraceSeparation.{v} := by
  intro K _ _ _ U _ _ _ τ hf hi hd
  by_contra! htrace
  have hm := exists_faithful_absolute_binary_model_of_binary_traces τ hf hi htrace
  rw [hd] at hm
  obtain ⟨σ, hfσ, hiσ⟩ := hm
  exact h σ hfσ hiσ

/-- The requested trace statement rules out absolutely irreducible binary
models, so the binary obstruction is necessary as well as sufficient. -/
theorem binaryExclusion_of_fourteenTraceSeparation (h : FourteenTraceSeparation.{0}) :
    BinaryFourteenExclusion := by
  intro σ hf hi
  obtain ⟨g, hg⟩ := h (ZMod 2) (Fin 14 → ZMod 2) σ hf hi (by simp)
  exact hg (ZMod.pow_card (σ.character g))

/-- Over universe zero the source trace contract is equivalent to the concrete
binary obstruction. Neither side is asserted by this equivalence. -/
theorem fourteenTraceSeparation_iff_binaryExclusion :
    FourteenTraceSeparation.{0} ↔ BinaryFourteenExclusion :=
  ⟨binaryExclusion_of_fourteenTraceSeparation, fourteenTraceSeparation_of_binaryExclusion⟩

/-- Apply the local restriction calculation to the actual descended model.
This supplies the dimension-two input to the proposed corner-algebra argument;
it does not assume a representation-identification theorem. -/
theorem exists_binary_model_with_five_fixed_space (hfixed : FiveFixedSpaceTwo)
    {K U : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K Carrier U) (hf : Function.Injective τ)
    (hi : τ.IsAbsolutelyIrreducible) (hd : Module.finrank K U = 14)
    (htrace : ∀ g, τ.character g ^ 2 = τ.character g) :
    ∃ (P : Subgroup Carrier), Nat.card P = 25 ∧
      ∃ σ : Representation (ZMod 2) Carrier (Fin 14 → ZMod 2),
        Function.Injective σ ∧ σ.IsAbsolutelyIrreducible ∧
          Module.finrank (ZMod 2) (invariants (σ.comp P.subtype)) = 2 := by
  obtain ⟨P, hP, hfix⟩ := hfixed
  have hm := exists_faithful_absolute_binary_model_of_binary_traces τ hf hi htrace
  rw [hd] at hm
  obtain ⟨σ, hfσ, hiσ⟩ := hm
  exact ⟨P, hP, σ, hfσ, hiσ, hfix σ hfσ⟩

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
