module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryLayers
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSections
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Both section bounds for a mixed linear--unitary hexagon

The unitary root's nontrivial square lies in Φ(U_si). The linear reflection
moves that square. Below the linear degree bound the actual section action
would be trivial, so Φ(U_si) has order at least 2^(2a); the whole-radical
effective quotient has the same lower bound. Thus |U_si| ≥ 2^(4a).

Combined with the two unitary layers and the literal five-root orders,
this gives 2n ≤ a and 2a ≤ 9n. The earlier square profile also forces
a and n to have the same parity. These are the initial restrictions in
Fong--Seitz I (6D), printed p.43, on actual source radicals and actions.
The later derived/centralizer and lower-central-series contradictions
are still required. In particular these bounds do not exclude the row.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates GTwoSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {E : Type*} [Field E] [Finite E] [CharP E 2]

/-- A square from the opposite nonlinear root supplies the second linear
section on the same radical. Perfectness of original factors is not used. -/
theorem linear_two_layer_bound_of_opposite_square
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* PSL(2,E)) (s : RootReflection Q split j)
    {a : ℕ} (ha : 1 < a) (hE : Nat.card E = 2^a)
    (hsquare : ∃ x : simpleRoot Q split i, x^2 ≠ 1) :
    2^(4*a) ≤ Nat.card (simpleRemainder Q split j) := by
  let d := radicalSection Q split j hKj
  let f := frattiniSection Q split j d
  have h1 := linear_effectiveSection_card_bound Q split j hKj μj s d
    (d.effectiveRepresentation_injective
      (linear_radical_effectiveAction_injective Q split j hKj μj s hhex i hij hKi)) ha hE
  have he : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]; exact sup_bot_eq _
  change 2^(2*a) ≤ d.effectiveDenominator.index at h1
  rw [he] at h1
  have hmove : f.action ≠ 1 := by
    obtain ⟨x,hx⟩ := hsquare
    intro hz
    exact reflection_moves_frattini_radical Q split hhex i j hij s hKj x hx
      (by rw [hz]; rfl)
  have h2 : 2^(2*a) ≤ Nat.card f.Carrier := by
    by_contra! hsmall
    exact hmove (linear_small_section_action Q split j hKj μj s f ha hE hsmall)
  have hc : Nat.card f.Carrier = Nat.card (frattini d.numerator) := by
    change Nat.card (f.numerator ⧸ (⊥ : Subgroup f.numerator)) = _
    rw [Nat.card_congr (QuotientGroup.quotientBot (G := f.numerator)).toEquiv]
    exact Nat.card_congr ((frattini d.numerator).equivMapOfInjective
      d.numerator.subtype d.numerator.subtype_injective).symm.toEquiv
  rw [hc] at h2
  calc
    2^(4*a) = 2^(2*a)*2^(2*a) := by rw [←pow_add]; congr 1; omega
    _ ≤ Nat.card (d.numerator ⧸ frattini d.numerator)*Nat.card (frattini d.numerator) :=
      Nat.mul_le_mul h1 h2
    _ = Nat.card d.numerator := (frattini d.numerator).index_mul_card

/-- Square-product profile (1J) for the two exact binary root orders. -/
theorem mixed_unitary_square_profile_parity {a n : ℕ}
    (hsquare : IsSquare (2^a * (2^n)^3)) : a % 2 = n % 2 := by
  obtain ⟨k,hk⟩ := hsquare
  have hp := Nat.BinaryTorusParity.two_pow_mod_three (a+3*n)
  have he : 2^a*(2^n)^3 = 2^(a+3*n) := by
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  rw [he] at hk
  have hs := congrArg (fun x : ℕ => x%3) hk
  rw [Nat.mul_mod] at hs
  by_contra hn
  have hodd : (a+3*n)%2 ≠ 0 := by omega
  rw [if_neg hodd] at hp
  rw [hp] at hs
  have hk3 : k%3 = 0 ∨ k%3 = 1 ∨ k%3 = 2 := by omega
  rcases hk3 with hk3 | hk3 | hk3 <;> norm_num [hk3] at hs

/-- Both initial (6D) inequalities use the canonical radicals, the actual
unitary cover, and its constructed root-square input. -/
theorem mixed_linear_unitary_parameter_bounds
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {a : ℕ} (hE : Nat.card E = 2^a)
    (hsquare : ∃ x : simpleRoot Q split j, x^2 ≠ 1)
    (hroot : Nat.card (simpleRoot Q split j) = (2^n)^3) :
    2*n ≤ a ∧ 2*a ≤ 9*n := by
  have hi : Nat.card (simpleRoot Q split i) = 2^a :=
    (simpleRoot_card Q split i hKi μi).trans hE
  have hlo := unitary_hexagon_parameter_bound J hn hcard hconj Q split j σ hσ
    hhex i hij sj hKj hsquare hroot hi
  refine ⟨hlo,?_⟩
  have hb := linear_two_layer_bound_of_opposite_square Q split hhex j i hij.symm
    hKj hKi μi si (by omega) hE hsquare
  have hU : Nat.card split.U = (2^a*(2^n)^3)^3 := by
    have hu := unipotent_card_even Q split 3 hhex
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact (hij rfl).elim
    · rwa [hi,hroot] at hu
    · rwa [hroot,hi,mul_comm ((2^n)^3) (2^a)] at hu
    · exact (hij rfl).elim
  have hV : Nat.card (simpleRemainder Q split i) = 2^(2*a+9*n) := by
    have hh := unipotent_card_simple Q split i
    rw [hU,hi] at hh
    apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 2))
    calc
      2^a * Nat.card (simpleRemainder Q split i) = (2^a*(2^n)^3)^3 := hh.symm
      _ = 2^a * 2^(2*a+9*n) := by
        simp only [←pow_mul,←pow_add]
        congr 1
        omega
  rw [hV] at hb
  have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
