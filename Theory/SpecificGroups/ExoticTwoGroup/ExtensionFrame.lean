module

public import Theory.SpecificGroups.ExoticTwoGroup.Presentation

/-!+# The action and lift stages of exotic extension recognition

An action frame records a marked C₄-square base and generators whose
conjugation on that base agrees with Janko–Thompson 1.4(c), printed p.386.
It does not assert that the outer lifts are involutions or that they have
the required conjugation on the inner complement. These remaining lift
relations are a separate predicate. Together the two pieces give precisely
the existing presentation, including generation and the marked four.

Existence of either piece is a recognition obligation, not an instance or
an assumed classification theorem.
-/

namespace ExoticTwoGroup

/-- A basis, an inner elementary complement, and lifts of the prescribed
outer actions. No relations on the squares of the outer lifts are assumed. -/
public structure ActionFrame {P : Type*} [Group P] (D W B : Subgroup P) where
  a : P
  b : P
  g₁ : P
  g₂ : P
  t : P
  z₀ : P
  a_four : a ^ 4 = 1
  b_four : b ^ 4 = 1
  ab : Commute a b
  base : D = Subgroup.closure ({a, b} : Set P)
  four : W = Subgroup.closure ({a ^ 2, b ^ 2} : Set P)
  g₁_mem : g₁ ∈ B
  g₂_mem : g₂ ∈ B
  g₁_two : g₁ ^ 2 = 1
  g₂_two : g₂ ^ 2 = 1
  g₁g₂ : Commute g₁ g₂
  g₁_a : g₁ * a * g₁⁻¹ = a⁻¹
  g₁_b : g₁ * b * g₁⁻¹ = a ^ 2 * b⁻¹
  g₂_a : g₂ * a * g₂⁻¹ = a⁻¹ * b ^ 2
  g₂_b : g₂ * b * g₂⁻¹ = b⁻¹
  z₀_a : z₀ * a * z₀⁻¹ = a⁻¹
  z₀_b : z₀ * b * z₀⁻¹ = b⁻¹
  t_a : t * a * t⁻¹ = b
  t_b : t * b * t⁻¹ = a
  generate : Subgroup.closure ({a, b, g₁, g₂, t, z₀} : Set P) = ⊤

namespace ActionFrame

/-- The relations still required after the action on the abelian base
has been identified. They may require changing the chosen lifts. -/
public structure LiftRelations {P : Type*} [Group P] {D W B : Subgroup P}
    (f : ActionFrame D W B) : Prop where
  t_two : f.t ^ 2 = 1
  z₀_two : f.z₀ ^ 2 = 1
  tz₀ : Commute f.t f.z₀
  z₀_g₁ : f.z₀ * f.g₁ * f.z₀⁻¹ = f.a * f.g₁
  z₀_g₂ : f.z₀ * f.g₂ * f.z₀⁻¹ = f.b * f.g₂
  t_g₁ : f.t * f.g₁ * f.t⁻¹ = f.g₂
  t_g₂ : f.t * f.g₂ * f.t⁻¹ = f.g₁

/-- Assemble the exact presentation once the lift relations have been proved. -/
public def toPresentation {P : Type*} [Group P] {D W B : Subgroup P}
    (f : ActionFrame D W B) (h : f.LiftRelations) (hcard : Nat.card P = 256) :
    Presentation P where
  a := f.a
  b := f.b
  g₁ := f.g₁
  g₂ := f.g₂
  t := f.t
  z₀ := f.z₀
  a_four := f.a_four
  b_four := f.b_four
  ab := f.ab
  g₁_two := f.g₁_two
  g₂_two := f.g₂_two
  g₁g₂ := f.g₁g₂
  g₁_a := f.g₁_a
  g₁_b := f.g₁_b
  g₂_a := f.g₂_a
  g₂_b := f.g₂_b
  t_two := h.t_two
  z₀_two := h.z₀_two
  tz₀ := h.tz₀
  z₀_a := f.z₀_a
  z₀_b := f.z₀_b
  z₀_g₁ := h.z₀_g₁
  z₀_g₂ := h.z₀_g₂
  t_a := f.t_a
  t_b := f.t_b
  t_g₁ := h.t_g₁
  t_g₂ := h.t_g₂
  generate := f.generate
  card := hcard

/-- Assembly preserves the specified normal four. -/
public theorem exists_presentation {P : Type*} [Group P] {D W B : Subgroup P}
    (f : ActionFrame D W B) (h : f.LiftRelations) (hcard : Nat.card P = 256) :
    ∃ d : Presentation P, W = Subgroup.closure ({d.a ^ 2, d.b ^ 2} : Set P) :=
  ⟨f.toPresentation h hcard, f.four⟩

end ActionFrame
end ExoticTwoGroup
