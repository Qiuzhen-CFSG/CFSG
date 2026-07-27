module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.GroupTheory.GroupAction.Quotient

open scoped BigOperators

namespace Representation

attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G]

/-- Complex-valued class functions on `G`, implemented as functions on conjugacy classes. -/
public abbrev ClassFunction (G : Type*) [Group G] := ConjClasses G → ℂ

/-- Turn a complex-valued function on `G` that is constant on conjugacy classes into a class function. -/
@[expose] public noncomputable def classFunctionOfInvariant (f : G → ℂ)
    (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) : ClassFunction G := by
  refine Quotient.lift f ?_
  intro a b hab
  rcases hab with ⟨c, hc⟩
  have hconj : (↑c : G) * a * ↑(c⁻¹) = b := by
    calc
      (↑c : G) * a * ↑(c⁻¹) = (b * ↑c) * ↑(c⁻¹) := by rw [hc.eq]
      _ = b := by simp [mul_assoc]
  calc
    f a = f ((↑c : G) * a * ↑(c⁻¹)) := by simpa using (hf a c).symm
    _ = f b := by rw [hconj]

/-- The class function attached to a representation character. -/
@[expose] public noncomputable def characterClassFunction {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) : ClassFunction G :=
  classFunctionOfInvariant ρ.character (by
    intro g h
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g h)

/-- Inner product of complex class functions, normalized by `|G|`. -/
@[expose] public noncomputable def classFunctionInner [Finite G]
    (φ ψ : ClassFunction G) : ℂ := by
  classical
  letI := Fintype.ofFinite G
  exact (Nat.card G : ℂ)⁻¹ * ∑ g : G, φ (ConjClasses.mk g) * star (ψ (ConjClasses.mk g))

/-- A complex class function on `G` is a character if it comes from a finite-dimensional
representation, encoded on the standard space `Fin n → ℂ`. -/
@[expose] public def IsCharacter [Finite G] (χ : ClassFunction G) : Prop :=
  ∃ n : ℕ, ∃ ρ : Representation ℂ G (Fin n → ℂ), χ = characterClassFunction ρ

/-- A complex class function on `G` is irreducible if it is a character of norm one. -/
@[expose] public def IsIrreducibleCharacter [Finite G] (χ : ClassFunction G) : Prop :=
  IsCharacter χ ∧ classFunctionInner χ χ = 1

/-- A finite family of class functions containing each irreducible complex character
exactly once. -/
@[expose] public def IsCompleteIrreducibleCharacterFamily [Finite G]
    {ι : Type*} [Fintype ι] (χ : ι → ClassFunction G) : Prop :=
  (∀ i, IsIrreducibleCharacter (χ i)) ∧
    (∀ χ₀ : ClassFunction G, IsIrreducibleCharacter χ₀ → ∃ i, χ i = χ₀) ∧
    Function.Injective χ

end Representation
