module

public import Theory.Representation.SymplecticConjugatePair.OddOrder
public import Theory.Representation.SymplecticConjugatePair.OddOrder.Binary.FixedSpaces
public import Theory.Representation.SymplecticConjugatePair.OddOrder.Binary.Automorphisms

/-!
# The binary strengthening for a symplectic natural module and its twist

Over a field of order two, every automorphism moving the diagram is inner times
the exceptional graph map. An element of order three with nonzero natural fixed
space is sent by that map to one with zero fixed space. Thus the two natural
summands have total codimension at least six. Every other odd prime has zero
fixed space on both summands and total codimension eight.

These statements use the actual matrix automorphism, natural fixed submodules,
and paired binary representation. They require no automorphism-coverage premise.
They prove the matrix-model assertion in Aschbacher–Smith H.7, printed p.389 of
`refs/quasithin.pdf`, combined manuscript of 1 March 2004. Transport from a larger
acting group and the final source β statement belong to the chapter assembly.
-/

public section

namespace SymplecticConjugatePair.OddOrder.Binary
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open Representation.BinaryOffender Module
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- An order-three actor is fixed-point-free on one of the actual natural summands. -/
theorem naturalFixed_eq_bot_or_twist_of_order_three (hF : Nat.card F = 2)
    (τ : MulAut (Sp F)) (hτ : ¬ PreservesDiagram τ) {g : Sp F} (hg : orderOf g = 3) :
    naturalFixed g = ⊥ ∨ naturalFixed (τ g) = ⊥ := by
  by_cases h : naturalFixed g = ⊥
  · exact Or.inl h
  · obtain ⟨k, rfl⟩ := binary_moving_eq_inner_graph hF τ hτ
    right
    change naturalFixed (k * graphAut g * k⁻¹) = ⊥
    exact (naturalFixed_conj_eq_bot_iff k (graphAut g)).mpr
      (graph_fixed_eq_bot_of_order_three hF hg h)

omit [Finite F] [CharP F 2] in
private theorem codim_of_bot {g : Sp F} (h : naturalFixed g = ⊥) :
    finrank F (Vector F ⧸ naturalFixed g) = 4 := by
  have hd := (naturalFixed g).finrank_quotient_add_finrank
  have hz : finrank F (naturalFixed g) = 0 := Submodule.finrank_eq_zero.mpr h
  have hv : finrank F (Vector F) = 4 := by
    simp [Theory.SpecificGroups.SymplecticFour.Vector]
  omega

variable [Algebra (ZMod 2) F]

/-- Every other odd prime has the maximal paired codimension, independently of the twist. -/
theorem fixedCodim_eq_eight_of_prime_ne_three (hF : Nat.card F = 2)
    (τ : MulAut (Sp F)) {g : Sp F} (hp : (orderOf g).Prime) (ho : Odd (orderOf g))
    (h3 : orderOf g ≠ 3) : fixedCodim (binaryPair τ) (Subgroup.zpowers g) = 8 := by
  have h1 := naturalFixed_eq_bot_of_prime_ne_three hF hp ho h3
  have h2 := naturalFixed_eq_bot_of_prime_ne_three hF
    (g := τ g) (by rwa [τ.orderOf_eq]) (by rwa [τ.orderOf_eq]) (by rwa [τ.orderOf_eq])
  rw [binaryPair_fixedCodim, coefficient_finrank (n := 1) (by simpa using hF),
    codim_of_bot h1, codim_of_bot h2]

/-- H.7's binary bound for every odd-prime actor of the actual matrix group. -/
theorem six_le_fixedCodim (hF : Nat.card F = 2) (τ : MulAut (Sp F))
    (hτ : ¬ PreservesDiagram τ) {g : Sp F} (hp : (orderOf g).Prime)
    (ho : Odd (orderOf g)) : 6 ≤ fixedCodim (binaryPair τ) (Subgroup.zpowers g) := by
  by_cases h3 : orderOf g = 3
  · have hg : g ≠ 1 := fun h => hp.ne_one (by simp [h])
    have ht : τ g ≠ 1 := fun h => hg (τ.injective (h.trans τ.map_one.symm))
    have h1 := natural_codim_cases hg ho
    have h2 := natural_codim_cases ht (by rwa [τ.orderOf_eq])
    rw [binaryPair_fixedCodim, coefficient_finrank (n := 1) (by simpa using hF), one_mul]
    rcases naturalFixed_eq_bot_or_twist_of_order_three hF τ hτ h3 with h | h
    · rw [codim_of_bot h]
      omega
    · rw [codim_of_bot h]
      omega
  · rw [fixedCodim_eq_eight_of_prime_ne_three hF τ hp ho h3]
    decide

end SymplecticConjugatePair.OddOrder.Binary
